const http = require('http');
const https = require('https');
const net = require('net');
const tls = require('tls');
const crypto = require('crypto');
const zlib = require('zlib');
const dnsCb = require('dns');
const dns = dnsCb.promises;
const { domainToASCII } = require('url');

const PORT = process.env.PORT || 3000;
const SUPPORT = 'https://discord.gg/apitr';
const LIMIT = 60;
const CACHE_TTL = 5 * 60 * 1000;
const TRUST_PROXY = process.env.TRUST_PROXY === '1' || process.env.VERCEL === '1';
const MAX_TEXT = 10000;

const cache = new Map();
const hits = new Map();

const safe = (p, fallback = []) => p.catch(() => fallback);
const days = (ms) => Math.floor(ms / 864e5);
const fn = (e) => e.vcardArray?.[1]?.find((v) => v[0] === 'fn')?.[3] || null;
const mail = (e) => e.vcardArray?.[1]?.find((v) => v[0] === 'email')?.[3] || null;
const fail = (status, message) => Object.assign(new Error(message), { status });
const clamp = (n, min, max) => Math.min(max, Math.max(min, n));
const int = (v, def) => { const n = Number.parseInt(v, 10); return Number.isNaN(n) ? def : n; };
const dec = (s) => { try { return decodeURIComponent(s); } catch { throw fail(400, 'Geçersiz URL kodlaması'); } };

function cleanDomain(input) {
  try {
    const d = domainToASCII(decodeURIComponent(input).trim().toLowerCase().replace(/^https?:\/\//, '').split(/[/?#:]/)[0]);
    return /^(?=.{1,253}$)([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z0-9-]{2,63}$/.test(d) ? d : null;
  } catch { return null; }
}

function cleanIp(input) {
  try { const ip = decodeURIComponent(input).trim(); return net.isIP(ip) ? ip : null; } catch { return null; }
}

function toText(obj, ind = '') {
  const lines = [];
  for (const [k, v] of Object.entries(obj)) {
    if (v === null || v === undefined) lines.push(`${ind}${k}: -`);
    else if (Array.isArray(v)) {
      if (!v.length) lines.push(`${ind}${k}: -`);
      else if (v.length === 1 && typeof v[0] !== 'object') lines.push(`${ind}${k}: ${v[0]}`);
      else {
        lines.push(`${ind}${k}:`);
        for (const item of v) {
          if (typeof item === 'object' && item !== null) lines.push(`${ind}  -`, toText(item, ind + '    '));
          else lines.push(`${ind}  - ${item}`);
        }
      }
    } else if (typeof v === 'object') {
      if (!Object.keys(v).length) lines.push(`${ind}${k}: -`);
      else lines.push(`${ind}${k}:`, toText(v, ind + '  '));
    } else if (typeof v === 'string' && v.includes('\n')) {
      lines.push(`${ind}${k}:`, ...v.split(/\r?\n/).map((l) => `${ind}  ${l}`));
    } else lines.push(`${ind}${k}: ${v}`);
  }
  return lines.join('\n');
}

const CORS = { 'access-control-allow-origin': '*' };

function send(res, code, body) {
  res.writeHead(code, { 'content-type': 'text/plain; charset=utf-8', ...CORS });
  res.end(toText({ ...body, support: SUPPORT }) + '\n');
}

function sendRaw(res, type, body) {
  res.writeHead(200, { 'content-type': type, ...CORS });
  res.end(body);
}

function sendJson(res, code, body) {
  res.writeHead(code, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store', ...CORS });
  res.end(JSON.stringify(body) + '\n');
}

const RESERVED = [
  ['0.0.0.0', 8, 'ipv4', 'Ayrılmış (bu ağ)'],
  ['10.0.0.0', 8, 'ipv4', 'Özel ağ (private)'],
  ['100.64.0.0', 10, 'ipv4', 'CGNAT (paylaşımlı)'],
  ['127.0.0.0', 8, 'ipv4', 'Loopback'],
  ['169.254.0.0', 16, 'ipv4', 'Link-local'],
  ['172.16.0.0', 12, 'ipv4', 'Özel ağ (private)'],
  ['192.0.0.0', 24, 'ipv4', 'Ayrılmış (IETF)'],
  ['192.0.2.0', 24, 'ipv4', 'Dokümantasyon'],
  ['192.168.0.0', 16, 'ipv4', 'Özel ağ (private)'],
  ['198.18.0.0', 15, 'ipv4', 'Test ağı'],
  ['198.51.100.0', 24, 'ipv4', 'Dokümantasyon'],
  ['203.0.113.0', 24, 'ipv4', 'Dokümantasyon'],
  ['224.0.0.0', 4, 'ipv4', 'Multicast'],
  ['240.0.0.0', 4, 'ipv4', 'Ayrılmış'],
  ['::', 128, 'ipv6', 'Belirsiz adres'],
  ['::1', 128, 'ipv6', 'Loopback'],
  ['::ffff:0:0', 96, 'ipv6', 'IPv4-mapped'],
  ['64:ff9b::', 96, 'ipv6', 'NAT64'],
  ['2001:db8::', 32, 'ipv6', 'Dokümantasyon'],
  ['fc00::', 7, 'ipv6', 'Özel ağ (ULA)'],
  ['fe80::', 10, 'ipv6', 'Link-local'],
  ['ff00::', 8, 'ipv6', 'Multicast'],
].map(([addr, prefix, family, label]) => {
  const bl = new net.BlockList();
  bl.addSubnet(addr, prefix, family);
  return { bl, family, label };
});

function reservedLabel(ip) {
  const family = net.isIPv6(ip) ? 'ipv6' : 'ipv4';
  return RESERVED.find((r) => r.family === family && r.bl.check(ip, family))?.label || null;
}

function isPrivateIp(ip) {
  const clean = String(ip).replace(/^\[|\]$/g, '').split('%')[0];
  return net.isIP(clean) ? !!reservedLabel(clean) : true;
}

function safeLookup(hostname, options, cb) {
  dnsCb.lookup(hostname, options, (err, address, family) => {
    if (err) return cb(err);
    const list = Array.isArray(address) ? address : [{ address, family }];
    if (list.some((a) => isPrivateIp(a.address))) {
      return cb(Object.assign(new Error('Özel/yerel IP adreslerine erişim engellendi'), { code: 'BLOCKED' }));
    }
    cb(null, address, family);
  });
}

function probe(urlStr) {
  return new Promise((resolve, reject) => {
    let u;
    try { u = new URL(urlStr); } catch { return reject(fail(400, 'Geçersiz URL')); }
    if (!['http:', 'https:'].includes(u.protocol)) return reject(fail(400, 'Sadece http ve https desteklenir'));
    if (!['', '80', '443', '8080', '8443'].includes(u.port)) return reject(fail(400, 'Bu port desteklenmiyor (80, 443, 8080, 8443)'));
    const host = u.hostname.replace(/^\[|\]$/g, '');
    if (net.isIP(host) && isPrivateIp(host)) return reject(fail(400, 'Özel/yerel IP adreslerine erişim engellendi'));

    const lib = u.protocol === 'https:' ? https : http;
    const t0 = Date.now();
    const req = lib.request(u, {
      method: 'GET',
      lookup: safeLookup,
      agent: false,
      timeout: 8000,
      rejectUnauthorized: false,
      headers: { 'user-agent': 'DomainIpAPI/1.0 (+https://discord.gg/apitr)', accept: '*/*' },
    }, (res) => {
      const s = res.socket;
      const info = {
        url: u.href,
        status: res.statusCode,
        headers: res.headers,
        http_version: res.httpVersion,
        ms: Date.now() - t0,
        tls: u.protocol === 'https:'
          ? { valid: !!s.authorized, error: s.authorizationError ? String(s.authorizationError) : null, protocol: s.getProtocol?.() || null }
          : null,
      };
      res.destroy();
      resolve(info);
    });
    req.on('timeout', () => req.destroy(Object.assign(new Error('zaman aşımı'), { code: 'ETIMEDOUT' })));
    req.on('error', (e) => {
      if (e.code === 'BLOCKED' || /Özel\/yerel/.test(e.message)) return reject(fail(400, 'Özel/yerel IP adreslerine erişim engellendi'));
      reject(fail(502, `Bağlantı hatası: ${e.code || e.message}`));
    });
    req.end();
  });
}

async function trace(startUrl, max = 10) {
  const chain = [];
  let url = startUrl;
  for (let i = 0; i <= max; i++) {
    const r = await probe(url);
    chain.push(r);
    const loc = r.headers.location;
    if (r.status >= 300 && r.status < 400 && loc) {
      try { url = new URL(loc, r.url).href; } catch { return { chain, final: r }; }
      continue;
    }
    return { chain, final: r };
  }
  throw fail(502, `Çok fazla yönlendirme (${max} üzerinde)`);
}

let domainBoot = { at: 0, map: new Map() };
async function rdapDomainServer(tld) {
  if (!domainBoot.map.size || Date.now() - domainBoot.at > 864e5) {
    const j = await (await fetch('https://data.iana.org/rdap/dns.json')).json();
    const map = new Map();
    for (const [tlds, urls] of j.services) for (const t of tlds) map.set(t, urls[0]);
    domainBoot = { at: Date.now(), map };
  }
  return domainBoot.map.get(tld);
}

function port43(server, q) {
  return new Promise((resolve, reject) => {
    const s = net.connect(43, server);
    let buf = '';
    s.setTimeout(8000, () => { s.destroy(); reject(new Error('whois zaman aşımı')); });
    s.on('connect', () => s.write(q + '\r\n'));
    s.on('data', (d) => (buf += d));
    s.on('end', () => resolve(buf));
    s.on('error', reject);
  });
}

async function whois(domain) {
  const tld = domain.split('.').pop();
  let base;
  try { base = await rdapDomainServer(tld); } catch (e) { throw fail(502, 'RDAP listesi alınamadı: ' + e.message); }

  if (base) {
    const r = await fetch(`${base}domain/${domain}`, { headers: { accept: 'application/rdap+json' } });
    if (r.status === 404) return { domain, registered: false, available: true };
    if (!r.ok) throw fail(502, `RDAP hata: ${r.status}`);
    const d = await r.json();
    const ev = (a) => (d.events || []).find((e) => e.eventAction === a)?.eventDate || null;
    const created = ev('registration'), expires = ev('expiration');
    const reg = (d.entities || []).find((e) => (e.roles || []).includes('registrar'));
    const contacts = (d.entities || [])
      .filter((e) => !(e.roles || []).includes('registrar'))
      .map((e) => ({ role: (e.roles || []).join(','), name: fn(e), email: mail(e) }))
      .filter((c) => c.name && !/redacted|privacy/i.test(c.name));
    return {
      domain: d.ldhName?.toLowerCase() || domain,
      registered: true,
      available: false,
      registrar: reg ? fn(reg) : null,
      created,
      updated: ev('last changed'),
      expires,
      age_days: created ? days(Date.now() - new Date(created)) : null,
      days_left: expires ? days(new Date(expires) - Date.now()) : null,
      status: d.status || [],
      nameservers: (d.nameservers || []).map((n) => n.ldhName?.toLowerCase()),
      dnssec: d.secureDNS?.delegationSigned ?? null,
      contacts,
    };
  }

  try {
    const iana = await port43('whois.iana.org', tld);
    const server = iana.match(/^whois:\s*(\S+)/im)?.[1];
    if (!server) throw new Error('Bu uzantı için whois sunucusu bulunamadı');
    const raw = (await port43(server, domain)).trim();
    const registered = !/no match|not found|no entries found|no data found|available/i.test(raw);
    return { domain, registered, available: !registered, whois_server: server, raw };
  } catch (e) { throw fail(502, e.message); }
}

async function availableInfo(domain) {
  const w = await whois(domain);
  return {
    domain,
    available: w.available,
    ...(w.registered ? { expires: w.expires ?? null, registrar: w.registrar ?? null } : {}),
  };
}

async function dnsInfo(domain) {
  const t0 = Date.now();
  const txtOf = (arr) => arr.map((c) => c.join(''));
  const [a, aaaa, mx, ns, txt, cname, soa, caa, dmarc] = await Promise.all([
    safe(dns.resolve4(domain)),
    safe(dns.resolve6(domain)),
    safe(dns.resolveMx(domain)),
    safe(dns.resolveNs(domain)),
    safe(dns.resolveTxt(domain)),
    safe(dns.resolveCname(domain)),
    safe(dns.resolveSoa(domain), null),
    safe(dns.resolveCaa(domain)),
    safe(dns.resolveTxt(`_dmarc.${domain}`)),
  ]);
  const txts = txtOf(txt);
  const reverse = {};
  await Promise.all([...a.slice(0, 3), ...aaaa.slice(0, 2)].map(async (ip) => { reverse[ip] = await safe(dns.reverse(ip)); }));
  return {
    domain,
    ip: a,
    ipv6: aaaa,
    cname,
    mx: mx.sort((x, y) => x.priority - y.priority).map((m) => `${m.priority} ${m.exchange}`),
    ns,
    txt: txts,
    spf: txts.find((t) => t.startsWith('v=spf1')) || null,
    dmarc: txtOf(dmarc).find((t) => t.startsWith('v=DMARC1')) || null,
    caa: caa.map((c) => {
      const tag = c.issue !== undefined ? 'issue' : c.issuewild !== undefined ? 'issuewild' : 'iodef';
      return `${tag} "${c[tag]}"`;
    }),
    soa: soa && { primary: soa.nsname, admin: soa.hostmaster, serial: soa.serial, refresh: soa.refresh, retry: soa.retry, expire: soa.expire, minttl: soa.minttl },
    reverse,
    took_ms: Date.now() - t0,
  };
}

async function resolveTarget(input) {
  const ip = cleanIp(input);
  if (ip) return { ip, domain: null };
  const domain = cleanDomain(input);
  if (!domain) throw fail(400, 'Geçersiz IP adresi veya alan adı');
  const a = await safe(dns.resolve4(domain));
  const aaaa = a.length ? [] : await safe(dns.resolve6(domain));
  const found = a[0] || aaaa[0];
  if (!found) throw fail(404, 'Alan adı IP adresine çözümlenemedi');
  return { ip: found, domain };
}

const ipBoot = {};
async function rdapIpServer(ip) {
  const v6 = net.isIPv6(ip);
  const key = v6 ? 'v6' : 'v4';
  if (!ipBoot[key] || Date.now() - ipBoot[key].at > 864e5) {
    const j = await (await fetch(`https://data.iana.org/rdap/ip${key}.json`)).json();
    ipBoot[key] = {
      at: Date.now(),
      list: j.services.map(([cidrs, urls]) => {
        const bl = new net.BlockList();
        for (const c of cidrs) { const [a, p] = c.split('/'); bl.addSubnet(a, +p, v6 ? 'ipv6' : 'ipv4'); }
        return { bl, url: urls.find((u) => u.startsWith('https')) || urls[0] };
      }),
    };
  }
  return ipBoot[key].list.find((s) => s.bl.check(ip, v6 ? 'ipv6' : 'ipv4'))?.url;
}

async function rdapIp(ip) {
  const base = await rdapIpServer(ip);
  if (!base) throw new Error('Bu IP için RDAP sunucusu bulunamadı');
  const r = await fetch(`${base}ip/${ip}`, { headers: { accept: 'application/rdap+json' } });
  if (!r.ok) throw new Error(`RDAP hata: ${r.status}`);
  const d = await r.json();
  const ev = (a) => (d.events || []).find((e) => e.eventAction === a)?.eventDate || null;
  const all = (d.entities || []).flatMap((e) => [e, ...(e.entities || [])]);
  const abuse = all.find((e) => (e.roles || []).includes('abuse'));
  return {
    name: d.name || null,
    handle: d.handle || null,
    range: d.startAddress && d.endAddress ? `${d.startAddress} - ${d.endAddress}` : null,
    cidr: (d.cidr0_cidrs || []).map((c) => `${c.v4prefix || c.v6prefix}/${c.length}`),
    country: d.country || null,
    type: d.type || null,
    org: all.map(fn).find(Boolean) || null,
    abuse_email: abuse ? mail(abuse) : null,
    created: ev('registration'),
    updated: ev('last changed'),
  };
}

async function ipInfo(input) {
  const { ip, domain } = await resolveTarget(input);
  const out = {
    ip,
    ...(domain ? { domain } : {}),
    version: net.isIPv6(ip) ? 6 : 4,
    type: reservedLabel(ip) || 'Genel (public)',
    reverse: await safe(dns.reverse(ip)),
  };
  if (!reservedLabel(ip)) {
    try { out.network = await rdapIp(ip); }
    catch (e) { out.network = null; out.network_error = e.message; }
  }
  return out;
}

function expandV6(input) {
  const ip = input.split('%')[0];
  if (ip.includes('.')) throw fail(400, 'IPv4 gömülü IPv6 adresleri desteklenmiyor');
  const [head, tail] = ip.split('::');
  const h = head ? head.split(':') : [];
  const t = tail ? tail.split(':') : [];
  const groups = ip.includes('::') ? [...h, ...Array(8 - h.length - t.length).fill('0'), ...t] : h;
  return groups.map((g) => g.padStart(4, '0')).join('');
}

async function asnInfo(input) {
  const { ip, domain } = await resolveTarget(input);
  const label = reservedLabel(ip);
  if (label) throw fail(400, `Bu IP genel değil (${label})`);
  const qname = net.isIPv6(ip)
    ? `${expandV6(ip).split('').reverse().join('.')}.origin6.asn.cymru.com`
    : `${ip.split('.').reverse().join('.')}.origin.asn.cymru.com`;
  let txt;
  try { txt = (await dns.resolveTxt(qname)).map((c) => c.join(''))[0]; }
  catch { throw fail(404, 'ASN bilgisi bulunamadı'); }
  if (!txt) throw fail(404, 'ASN bilgisi bulunamadı');
  const [asns, prefix, country, registry, allocated] = txt.split('|').map((s) => s.trim());
  const list = asns.split(/\s+/);
  let name = null;
  try {
    const t2 = (await dns.resolveTxt(`AS${list[0]}.asn.cymru.com`)).map((c) => c.join(''))[0];
    name = t2.split('|').pop().trim();
  } catch {}
  return {
    ip,
    ...(domain ? { domain } : {}),
    asn: `AS${list[0]}`,
    all_asns: list.map((a) => `AS${a}`),
    name,
    prefix,
    country,
    registry,
    allocated,
  };
}

const DNSBLS = ['zen.spamhaus.org', 'bl.spamcop.net', 'dnsbl-1.uceprotect.net', 'psbl.surriel.com', 'dnsbl.dronebl.org', 'ix.dnsbl.manitu.net'];

async function blacklist(input) {
  const { ip, domain } = await resolveTarget(input);
  if (net.isIPv6(ip)) throw fail(400, 'Kara liste kontrolü şimdilik sadece IPv4 destekler');
  const label = reservedLabel(ip);
  if (label) throw fail(400, `Bu IP genel değil (${label})`);
  const rev = ip.split('.').reverse().join('.');
  const resolver = new dns.Resolver({ timeout: 3000, tries: 1 });
  const results = await Promise.all(DNSBLS.map(async (zone) => {
    try {
      const a = await resolver.resolve4(`${rev}.${zone}`);
      if (a.some((x) => x.startsWith('127.255.255.'))) return [zone, 'belirsiz (liste bu çözücüden gelen sorguyu reddetti)'];
      return [zone, `LİSTELENMİŞ (${a[0]})`];
    } catch (e) {
      return [zone, ['ENOTFOUND', 'ENODATA'].includes(e.code) ? 'temiz' : `belirsiz (${e.code})`];
    }
  }));
  const listed = results.filter(([, s]) => s.startsWith('LİSTELENMİŞ')).length;
  return {
    ip,
    ...(domain ? { domain } : {}),
    blacklisted: listed > 0,
    listed_count: listed,
    checked: DNSBLS.length,
    lists: Object.fromEntries(results),
  };
}

async function sslInfo(domain) {
  let addrs;
  try { addrs = await dns.lookup(domain, { all: true }); } catch { throw fail(404, 'Alan adı çözümlenemedi'); }
  const addr = addrs.find((a) => !isPrivateIp(a.address));
  if (!addr) throw fail(400, 'Alan adı özel/yerel bir IP adresine çözümleniyor');

  return new Promise((resolve, reject) => {
    const sock = tls.connect({ host: addr.address, port: 443, servername: domain, rejectUnauthorized: false, timeout: 8000 }, () => {
      try {
        const c = sock.getPeerCertificate();
        if (!c || !c.valid_to) throw new Error('Sertifika alınamadı');
        const to = new Date(c.valid_to), from = new Date(c.valid_from);
        const san = (c.subjectaltname || '').split(/,\s*/).filter((s) => s.startsWith('DNS:')).map((s) => s.slice(4));
        const nameErr = tls.checkServerIdentity(domain, c);
        const left = days(to - Date.now());
        resolve({
          domain,
          ip: addr.address,
          valid: !!sock.authorized && !nameErr,
          error: sock.authorizationError ? String(sock.authorizationError) : nameErr ? 'Alan adı sertifikayla eşleşmiyor' : null,
          expired: to < Date.now(),
          days_left: left,
          valid_from: from.toISOString(),
          valid_to: to.toISOString(),
          subject: c.subject?.CN || null,
          issuer: [c.issuer?.O, c.issuer?.CN].filter(Boolean).join(' / ') || null,
          self_signed: ['DEPTH_ZERO_SELF_SIGNED_CERT', 'SELF_SIGNED_CERT_IN_CHAIN'].includes(sock.authorizationError),
          protocol: sock.getProtocol(),
          cipher: sock.getCipher()?.name || null,
          key_bits: c.bits || null,
          serial: c.serialNumber || null,
          fingerprint_sha256: c.fingerprint256 || null,
          san_count: san.length,
          san: san.slice(0, 50),
        });
      } catch (e) { reject(fail(502, e.message)); }
      sock.end();
    });
    sock.on('timeout', () => { sock.destroy(); reject(fail(504, 'TLS bağlantısı zaman aşımına uğradı')); });
    sock.on('error', (e) => reject(fail(502, `TLS bağlantı hatası: ${e.code || e.message}`)));
  });
}

const SECURITY_HEADERS = [
  'strict-transport-security',
  'content-security-policy',
  'x-frame-options',
  'x-content-type-options',
  'referrer-policy',
  'permissions-policy',
];

async function headersInfo(domain) {
  let t;
  try { t = await trace(`https://${domain}/`); }
  catch (e) {
    if (e.status !== 502) throw e;
    try { t = await trace(`http://${domain}/`); } catch { throw e; }
  }
  const f = t.final;
  const h = f.headers;
  const security = Object.fromEntries(SECURITY_HEADERS.map((k) => [k, h[k] || 'YOK']));
  const present = SECURITY_HEADERS.filter((k) => h[k]).length;
  return {
    domain,
    final_url: f.url,
    status: `${f.status} ${http.STATUS_CODES[f.status] || ''}`.trim(),
    http_version: f.http_version,
    response_ms: f.ms,
    redirects: t.chain.length - 1,
    chain: t.chain.map((c) => `${c.status} ${c.url}`),
    tls: f.tls,
    server: h.server || null,
    content_type: h['content-type'] || null,
    content_length: h['content-length'] || null,
    cache_control: h['cache-control'] || null,
    security,
    security_score: `${present}/${SECURITY_HEADERS.length}`,
    headers: h,
  };
}

async function expand(input) {
  let s = input.trim();
  if (/^[a-z][a-z0-9+.-]*:\/\//i.test(s) && !/^https?:\/\//i.test(s)) throw fail(400, 'Sadece http ve https desteklenir');
  if (!/^https?:\/\//i.test(s)) s = `https://${s}`;
  let u;
  try { u = new URL(s); } catch { throw fail(400, 'Geçersiz URL'); }
  const t0 = Date.now();
  const t = await trace(u.href);
  return {
    input,
    final_url: t.final.url,
    final_status: t.final.status,
    redirects: t.chain.length - 1,
    chain: t.chain.map((c) => `${c.status} ${c.url}`),
    took_ms: Date.now() - t0,
  };
}

const DISPOSABLE = new Set(['mailinator.com', 'guerrillamail.com', 'guerrillamail.net', 'guerrillamail.org', 'sharklasers.com', '10minutemail.com', '10minutemail.net', 'temp-mail.org', 'tempmail.com', 'tempmail.net', 'yopmail.com', 'yopmail.net', 'trashmail.com', 'trashmail.net', 'getnada.com', 'nada.email', 'throwawaymail.com', 'maildrop.cc', 'dispostable.com', 'fakeinbox.com', 'mintemail.com', 'mohmal.com', 'emailondeck.com', 'tempail.com', 'burnermail.io', 'spamgourmet.com', 'mytemp.email', 'tmpmail.org', 'tmpmail.net', 'discard.email', 'mailnesia.com', 'moakt.com', 'tempinbox.com', 'inboxkitten.com', 'emailfake.com', 'fakemail.net', 'luxusmail.org', 'mailcatch.com', 'mailtemp.net', 'minuteinbox.com']);
const FREE_PROVIDERS = new Set(['gmail.com', 'googlemail.com', 'outlook.com', 'hotmail.com', 'live.com', 'msn.com', 'yahoo.com', 'ymail.com', 'icloud.com', 'me.com', 'mac.com', 'aol.com', 'proton.me', 'protonmail.com', 'pm.me', 'gmx.com', 'gmx.net', 'mail.com', 'zoho.com', 'yandex.com', 'yandex.ru', 'mail.ru', 'hotmail.com.tr', 'outlook.com.tr', 'yahoo.com.tr', 'mynet.com', 'windowslive.com', 'tutanota.com', 'fastmail.com']);
const ROLE_ACCOUNTS = new Set(['admin', 'administrator', 'info', 'support', 'destek', 'iletisim', 'contact', 'sales', 'satis', 'noreply', 'no-reply', 'postmaster', 'webmaster', 'hostmaster', 'abuse', 'billing', 'hr', 'ik', 'office', 'hello', 'mail', 'help', 'security', 'team', 'root', 'marketing', 'press', 'jobs', 'career']);
const TYPO_TARGETS = ['gmail.com', 'hotmail.com', 'outlook.com', 'yahoo.com', 'icloud.com', 'yandex.com'];

function levenshtein(a, b) {
  const dp = Array.from({ length: a.length + 1 }, (_, i) => [i, ...Array(b.length).fill(0)]);
  for (let j = 0; j <= b.length; j++) dp[0][j] = j;
  for (let i = 1; i <= a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      dp[i][j] = Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    }
  }
  return dp[a.length][b.length];
}

async function mailInfo(raw) {
  const email = dec(raw).trim().toLowerCase();
  const at = email.lastIndexOf('@');
  const local = at > 0 ? email.slice(0, at) : '';
  const domain = at > 0 ? cleanDomain(email.slice(at + 1)) : null;
  const syntaxOk = email.length <= 254 && local.length > 0 && local.length <= 64 &&
    /^[a-z0-9.!#$%&'*+/=?^_`{|}~-]+$/.test(local) && !local.startsWith('.') && !local.endsWith('.') && !local.includes('..') && !!domain;
  if (!syntaxOk) return { email, valid_syntax: false, reason: 'E-posta biçimi geçersiz' };

  const [mx, a, aaaa] = await Promise.all([safe(dns.resolveMx(domain)), safe(dns.resolve4(domain)), safe(dns.resolve6(domain))]);
  const hasMx = mx.length > 0;
  const accepts = hasMx || a.length > 0 || aaaa.length > 0;
  const disposable = DISPOSABLE.has(domain);
  const free = FREE_PROVIDERS.has(domain);
  const role = ROLE_ACCOUNTS.has(local.split('+')[0]);

  let suggestion = null;
  if (!FREE_PROVIDERS.has(domain)) {
    const best = TYPO_TARGETS.map((t) => [t, levenshtein(domain, t)]).sort((x, y) => x[1] - y[1])[0];
    if (best && best[1] > 0 && best[1] <= 2) suggestion = `${local}@${best[0]}`;
  }

  let status = 'gecerli';
  if (!accepts) status = 'gecersiz (alan adı e-posta kabul etmiyor)';
  else if (disposable) status = 'riskli (tek kullanımlık adres)';
  else if (suggestion) status = 'riskli (yazım hatası olabilir)';

  return {
    email,
    valid_syntax: true,
    local,
    domain,
    status,
    accepts_mail: accepts,
    mx: mx.sort((x, y) => x.priority - y.priority).map((m) => `${m.priority} ${m.exchange}`),
    disposable,
    free_provider: free,
    role_account: role,
    suggestion,
  };
}

const IBAN_LEN = Object.fromEntries('AD24 AE23 AL28 AT20 AZ28 BA20 BE16 BG22 BH22 BR29 BY28 CH21 CR22 CY28 CZ24 DE22 DK18 DO28 EE20 EG29 ES24 FI18 FO18 FR27 GB22 GE22 GI23 GL18 GR27 GT28 HR21 HU28 IE22 IL23 IQ23 IS26 IT27 JO30 KW30 KZ20 LB28 LC32 LI21 LT20 LU20 LV21 MC27 MD24 ME22 MK19 MR27 MT31 MU30 NL18 NO15 PK24 PL28 PS29 PT25 QA29 RO24 RS22 SA24 SC31 SE24 SI19 SK24 SM27 ST25 SV28 TL23 TN24 TR26 UA29 VA22 VG24 XK20'.split(' ').map((s) => [s.slice(0, 2), +s.slice(2)]));

const TR_BANKS = {
  '00010': 'T.C. Ziraat Bankası', '00012': 'Halkbank', '00015': 'Vakıfbank', '00032': 'Türk Ekonomi Bankası (TEB)',
  '00046': 'Akbank', '00059': 'Şekerbank', '00062': 'Garanti BBVA', '00064': 'Türkiye İş Bankası',
  '00067': 'Yapı Kredi', '00099': 'ING Bank', '00103': 'Fibabanka', '00111': 'QNB',
  '00123': 'HSBC', '00124': 'Alternatifbank', '00134': 'DenizBank', '00135': 'Anadolubank',
  '00146': 'Odeabank', '00203': 'Albaraka Türk', '00205': 'Kuveyt Türk', '00206': 'Türkiye Finans',
  '00209': 'Ziraat Katılım', '00210': 'Vakıf Katılım', '00211': 'Emlak Katılım',
};

function ibanInfo(raw) {
  const iban = dec(raw).replace(/\s+/g, '').toUpperCase();
  if (!/^[A-Z]{2}\d{2}[A-Z0-9]{8,30}$/.test(iban)) return { valid: false, reason: 'IBAN biçimi geçersiz' };
  const country = iban.slice(0, 2);
  const expected = IBAN_LEN[country];
  const base = { iban: iban.replace(/(.{4})/g, '$1 ').trim(), country, check_digits: iban.slice(2, 4), length: iban.length };
  if (!expected) return { valid: false, ...base, reason: 'Ülke kodu desteklenmiyor' };
  if (iban.length !== expected) return { valid: false, ...base, reason: `Uzunluk hatalı (beklenen ${expected}, gelen ${iban.length})` };
  let rem = 0;
  for (const ch of iban.slice(4) + iban.slice(0, 4)) {
    rem = /\d/.test(ch) ? (rem * 10 + Number(ch)) % 97 : (rem * 100 + ch.charCodeAt(0) - 55) % 97;
  }
  if (rem !== 1) return { valid: false, ...base, reason: 'Kontrol basamağı hatalı' };
  const out = { valid: true, ...base };
  if (country === 'TR') {
    out.bank_code = iban.slice(4, 9);
    out.bank = TR_BANKS[out.bank_code] || null;
    out.account_no = iban.slice(10);
  }
  return out;
}

function tcknInfo(raw) {
  const s = dec(raw).trim();
  if (!/^\d{11}$/.test(s)) return { valid: false, reason: '11 haneli rakam olmalı' };
  if (s[0] === '0') return { valid: false, reason: 'İlk hane 0 olamaz' };
  const d = [...s].map(Number);
  const odd = d[0] + d[2] + d[4] + d[6] + d[8];
  const even = d[1] + d[3] + d[5] + d[7];
  if (((odd * 7 - even) % 10 + 10) % 10 !== d[9]) return { valid: false, reason: '10. hane hatalı' };
  if (d.slice(0, 10).reduce((a, b) => a + b, 0) % 10 !== d[10]) return { valid: false, reason: '11. hane hatalı' };
  return { valid: true, note: 'Sadece algoritma doğrulaması, kişi sorgulaması değildir' };
}

function vknInfo(raw) {
  const s = dec(raw).trim();
  if (!/^\d{10}$/.test(s)) return { valid: false, reason: '10 haneli rakam olmalı' };
  const d = [...s].map(Number);
  let sum = 0;
  for (let i = 0; i < 9; i++) {
    const tmp = (d[i] + 9 - i) % 10;
    let v = (tmp * 2 ** (9 - i)) % 9;
    if (tmp !== 0 && v === 0) v = 9;
    sum += v;
  }
  if ((10 - (sum % 10)) % 10 !== d[9]) return { valid: false, reason: 'Kontrol hanesi hatalı' };
  return { valid: true, note: 'Sadece algoritma doğrulaması, mükellef sorgulaması değildir' };
}

const RELIGIOUS = {
  2023: ['2023-04-21', '2023-06-28'],
  2024: ['2024-04-10', '2024-06-16'],
  2025: ['2025-03-30', '2025-06-06'],
  2026: ['2026-03-20', '2026-05-27'],
  2027: ['2027-03-09', '2027-05-16'],
};
const WEEKDAYS = ['Pazar', 'Pazartesi', 'Salı', 'Çarşamba', 'Perşembe', 'Cuma', 'Cumartesi'];
const isoOf = (d) => d.toISOString().slice(0, 10);
const addDays = (iso, n) => isoOf(new Date(Date.parse(`${iso}T00:00:00Z`) + n * 864e5));

function holidaysOf(year) {
  const map = new Map();
  const add = (date, name, half = false) => {
    const e = map.get(date) || { names: [], half: true };
    e.names.push(name);
    e.half = e.half && half;
    map.set(date, e);
  };
  add(`${year}-01-01`, 'Yılbaşı');
  add(`${year}-04-23`, 'Ulusal Egemenlik ve Çocuk Bayramı');
  add(`${year}-05-01`, 'Emek ve Dayanışma Günü');
  add(`${year}-05-19`, "Atatürk'ü Anma, Gençlik ve Spor Bayramı");
  add(`${year}-07-15`, 'Demokrasi ve Milli Birlik Günü');
  add(`${year}-08-30`, 'Zafer Bayramı');
  add(`${year}-10-28`, 'Cumhuriyet Bayramı Arifesi', true);
  add(`${year}-10-29`, 'Cumhuriyet Bayramı');
  const rel = RELIGIOUS[year];
  if (rel) {
    add(addDays(rel[0], -1), 'Ramazan Bayramı Arifesi', true);
    for (let i = 0; i < 3; i++) add(addDays(rel[0], i), `Ramazan Bayramı ${i + 1}. Gün`);
    add(addDays(rel[1], -1), 'Kurban Bayramı Arifesi', true);
    for (let i = 0; i < 4; i++) add(addDays(rel[1], i), `Kurban Bayramı ${i + 1}. Gün`);
  }
  return map;
}

const REL_NOTE = `Dini bayram tarihleri sadece ${Object.keys(RELIGIOUS)[0]}-${Object.keys(RELIGIOUS).at(-1)} için ekli, bu yıl için sadece sabit tatiller var`;

function tatilInfo(raw) {
  const s = dec(raw).trim();

  if (/^\d{4}$/.test(s)) {
    const year = +s;
    if (year < 2000 || year > 2100) throw fail(400, 'Yıl 2000-2100 arasında olmalı');
    const map = holidaysOf(year);
    const entries = [...map.entries()].sort((a, b) => a[0].localeCompare(b[0]));
    let work = 0, full = 0;
    for (let t = Date.UTC(year, 0, 1); new Date(t).getUTCFullYear() === year; t += 864e5) {
      const d = new Date(t), wd = d.getUTCDay();
      if (wd === 0 || wd === 6) continue;
      const h = map.get(isoOf(d));
      work += h ? (h.half ? 0.5 : 0) : 1;
      if (h && !h.half) full++;
    }
    return {
      year,
      holiday_count: entries.length,
      weekday_full_holidays: full,
      workdays: work,
      holidays: entries.map(([date, e]) => `${date} ${WEEKDAYS[new Date(`${date}T00:00:00Z`).getUTCDay()]}: ${e.names.join(' / ')}${e.half ? ' (yarım gün)' : ''}`),
      ...(RELIGIOUS[year] ? {} : { note: REL_NOTE }),
    };
  }

  const m = s.match(/^(\d{4})-(\d{2})-(\d{2})$/);
  if (m) {
    const [, y, mo, d] = m.map(Number);
    const dt = new Date(Date.UTC(y, mo - 1, d));
    if (dt.getUTCFullYear() !== y || dt.getUTCMonth() !== mo - 1 || dt.getUTCDate() !== d) throw fail(400, 'Geçersiz tarih');
    if (y < 2000 || y > 2100) throw fail(400, 'Yıl 2000-2100 arasında olmalı');
    const date = isoOf(dt);
    const h = holidaysOf(y).get(date);
    const wd = dt.getUTCDay();
    const weekend = wd === 0 || wd === 6;
    const isWork = (iso) => {
      const x = new Date(`${iso}T00:00:00Z`), w = x.getUTCDay();
      const hh = holidaysOf(x.getUTCFullYear()).get(iso);
      return w !== 0 && w !== 6 && !(hh && !hh.half);
    };
    let next = addDays(date, 1);
    for (let i = 0; i < 20 && !isWork(next); i++) next = addDays(next, 1);
    return {
      date,
      weekday: WEEKDAYS[wd],
      holiday: h ? h.names.join(' / ') : null,
      half_day: h ? h.half : false,
      weekend,
      workday: !weekend && !(h && !h.half),
      next_workday: `${next} ${WEEKDAYS[new Date(`${next}T00:00:00Z`).getUTCDay()]}`,
      ...(RELIGIOUS[y] ? {} : { note: REL_NOTE }),
    };
  }
  throw fail(400, 'Kullanım: /tatil/2026 veya /tatil/2026-10-29');
}

const asciiFold = (s) => s.replace(/ı/g, 'i').replace(/İ/g, 'I').normalize('NFD').replace(/[\u0300-\u036f]/g, '');

async function namaz(raw, ctx) {
  const city = asciiFold(dec(raw).trim());
  let country = asciiFold((ctx.q('ulke') || 'Turkey').trim());
  const nameRe = /^[A-Za-z][A-Za-z .'-]{1,39}$/;
  if (!nameRe.test(city)) throw fail(400, 'Geçersiz şehir adı');
  if (!nameRe.test(country)) throw fail(400, 'Geçersiz ülke adı');
  if (/^turkiye$/i.test(country)) country = 'Turkey';
  const tz0 = /^turkey$/i.test(country) ? 'Europe/Istanbul' : 'UTC';
  const date = new Intl.DateTimeFormat('en-GB', { timeZone: tz0, day: '2-digit', month: '2-digit', year: 'numeric' }).format(new Date()).replace(/\//g, '-');

  const key = `aladhan:${city.toLowerCase()}|${country.toLowerCase()}|${date}`;
  let data = cache.get(key)?.data;
  if (!data) {
    const url = `https://api.aladhan.com/v1/timingsByCity/${date}?city=${encodeURIComponent(city)}&country=${encodeURIComponent(country)}&method=13`;
    let r;
    try { r = await fetch(url, { signal: AbortSignal.timeout(8000) }); }
    catch { throw fail(502, 'Namaz vakti servisine ulaşılamadı'); }
    if (r.status === 400 || r.status === 404) throw fail(404, 'Şehir bulunamadı');
    if (!r.ok) throw fail(502, `Namaz vakti servisi hata verdi (${r.status})`);
    data = (await r.json()).data;
    if (!data?.timings) throw fail(502, 'Namaz vakti servisi geçersiz cevap verdi');
    cache.set(key, { at: Date.now(), data });
  }

  const hm = (s) => { const m = String(s).match(/(\d{1,2}):(\d{2})/); return m ? `${m[1].padStart(2, '0')}:${m[2]}` : null; };
  const names = [['imsak', 'Imsak'], ['gunes', 'Sunrise'], ['ogle', 'Dhuhr'], ['ikindi', 'Asr'], ['aksam', 'Maghrib'], ['yatsi', 'Isha']];
  const times = Object.fromEntries(names.map(([k, a]) => [k, hm(data.timings[a])]));

  const tz = data.meta?.timezone || tz0;
  const [nh, nm] = new Intl.DateTimeFormat('en-GB', { timeZone: tz, hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).format(new Date()).split(':').map(Number);
  const nowMin = nh * 60 + nm;
  const toMin = (t) => { const [h, m] = t.split(':').map(Number); return h * 60 + m; };
  let next = names.find(([k]) => times[k] && toMin(times[k]) > nowMin);
  let remain;
  if (next) remain = toMin(times[next[0]]) - nowMin;
  else { next = ['imsak (yarın)']; remain = 1440 - nowMin + toMin(times.imsak); }
  const h = data.date?.hijri;

  return {
    city,
    country,
    date: data.date?.gregorian?.date || date,
    hijri: h ? `${h.day} ${h.month?.en} ${h.year}` : null,
    method: 'Diyanet İşleri Başkanlığı',
    timezone: tz,
    ...times,
    next_prayer: next[0],
    time_left: `${Math.floor(remain / 60)} sa ${remain % 60} dk`,
  };
}

function textArg(ctx, parts) {
  const t = parts.length ? dec(parts.join('/')) : (ctx.q('text') ?? ctx.q('q') ?? '');
  if (!t) throw fail(400, 'Metin boş');
  if (t.length > MAX_TEXT) throw fail(400, `Metin çok uzun (en fazla ${MAX_TEXT} karakter)`);
  return t;
}

const HASH_ALGOS = ['md5', 'sha1', 'sha256', 'sha384', 'sha512'];

function hashRoute(_, ctx) {
  let algo = null, parts = ctx.rest;
  if (HASH_ALGOS.includes((parts[0] || '').toLowerCase())) { algo = parts[0].toLowerCase(); parts = parts.slice(1); }
  const text = textArg(ctx, parts);
  const key = ctx.q('key');
  if (key) {
    const a = algo || 'sha256';
    return { algorithm: `hmac-${a}`, hmac: crypto.createHmac(a, key).update(text).digest('hex'), text_length: text.length };
  }
  if (algo) return { algorithm: algo, hash: crypto.createHash(algo).update(text).digest('hex'), text_length: text.length };
  const out = { text_length: text.length, bytes: Buffer.byteLength(text) };
  for (const a of HASH_ALGOS) out[a] = crypto.createHash(a).update(text).digest('hex');
  return out;
}

function base64Route(_, ctx) {
  const action = (ctx.rest[0] || '').toLowerCase();
  if (!['encode', 'decode'].includes(action)) throw fail(400, 'Kullanım: /base64/encode/{metin} veya /base64/decode/{base64}');
  const text = textArg(ctx, ctx.rest.slice(1));
  if (action === 'encode') {
    const b = Buffer.from(text, 'utf8');
    return { base64: b.toString('base64'), base64url: b.toString('base64url'), bytes: b.length };
  }
  const s = text.replace(/\s+/g, '').replace(/-/g, '+').replace(/_/g, '/');
  if (!/^[A-Za-z0-9+/]*={0,2}$/.test(s) || s.length % 4 === 1) throw fail(400, 'Geçersiz base64');
  const buf = Buffer.from(s, 'base64');
  const out = buf.toString('utf8');
  return out.includes('\uFFFD')
    ? { binary: true, bytes: buf.length, hex: buf.toString('hex') }
    : { text: out, bytes: buf.length };
}

function urlRoute(_, ctx) {
  const action = (ctx.rest[0] || '').toLowerCase();
  if (!['encode', 'decode'].includes(action)) throw fail(400, 'Kullanım: /url/encode/{metin} veya /url/decode/{metin}');
  const parts = ctx.rest.slice(1);
  if (action === 'encode') return { result: encodeURIComponent(textArg(ctx, parts)) };
  const raw = parts.length ? parts.join('/') : (ctx.q('text') ?? ctx.q('q') ?? '');
  if (!raw) throw fail(400, 'Metin boş');
  if (raw.length > MAX_TEXT) throw fail(400, `Metin çok uzun (en fazla ${MAX_TEXT} karakter)`);
  return { result: dec(raw) };
}

function jwtRoute(_, ctx) {
  const token = textArg(ctx, ctx.rest).trim();
  const parts = token.split('.');
  if (parts.length !== 3 || !parts[0] || !parts[1]) throw fail(400, 'Geçersiz JWT (3 parça bekleniyor)');
  const parse = (p) => {
    try {
      const v = JSON.parse(Buffer.from(p, 'base64url').toString('utf8'));
      if (typeof v !== 'object' || v === null || Array.isArray(v)) throw new Error();
      return v;
    } catch { throw fail(400, 'JWT çözülemedi'); }
  };
  const header = parse(parts[0]), payload = parse(parts[1]);
  const iso = (n) => (typeof n === 'number' ? new Date(n * 1000).toISOString() : null);
  const now = Date.now() / 1000;
  return {
    algorithm: header.alg || null,
    type: header.typ || null,
    issued_at: iso(payload.iat),
    not_before: iso(payload.nbf),
    expires_at: iso(payload.exp),
    expired: typeof payload.exp === 'number' ? payload.exp < now : null,
    header,
    payload,
    signature_present: !!parts[2],
    note: 'İmza doğrulanmaz, sadece içerik çözülür',
  };
}

function uuid7() {
  const b = crypto.randomBytes(16);
  const ts = BigInt(Date.now());
  for (let i = 0; i < 6; i++) b[i] = Number((ts >> BigInt(40 - 8 * i)) & 0xffn);
  b[6] = (b[6] & 0x0f) | 0x70;
  b[8] = (b[8] & 0x3f) | 0x80;
  const h = b.toString('hex');
  return `${h.slice(0, 8)}-${h.slice(8, 12)}-${h.slice(12, 16)}-${h.slice(16, 20)}-${h.slice(20)}`;
}

function uuidRoute(_, ctx) {
  const count = clamp(int(ctx.q('adet'), 1), 1, 100);
  const v = ctx.q('v') || '4';
  if (!['4', '7'].includes(v)) throw fail(400, 'Sürüm 4 veya 7 olmalı');
  const list = Array.from({ length: count }, () => (v === '7' ? uuid7() : crypto.randomUUID()));
  return count === 1 ? { uuid: list[0], version: +v } : { version: +v, count, uuids: list };
}

function passwordRoute(_, ctx) {
  const len = clamp(int(ctx.q('uzunluk'), 16), 4, 128);
  const count = clamp(int(ctx.q('adet'), 1), 1, 50);
  const sets = ['abcdefghijklmnopqrstuvwxyz'];
  if (ctx.q('buyuk') !== '0') sets.push('ABCDEFGHIJKLMNOPQRSTUVWXYZ');
  if (ctx.q('rakam') !== '0') sets.push('0123456789');
  if (ctx.q('ozel') !== '0') sets.push('!@#$%^&*()-_=+[]{}:,.?');
  const all = sets.join('');
  const gen = () => {
    const chars = sets.map((s) => s[crypto.randomInt(s.length)]);
    while (chars.length < len) chars.push(all[crypto.randomInt(all.length)]);
    for (let i = chars.length - 1; i > 0; i--) {
      const j = crypto.randomInt(i + 1);
      [chars[i], chars[j]] = [chars[j], chars[i]];
    }
    return chars.join('');
  };
  const list = Array.from({ length: count }, gen);
  return {
    length: len,
    entropy_bits: Math.round(len * Math.log2(all.length)),
    ...(count === 1 ? { password: list[0] } : { passwords: list }),
  };
}

async function myipRoute(_, ctx) {
  if (!ctx.ip) throw fail(400, 'IP adresi belirlenemedi');
  return {
    ...(await ipInfo(ctx.ip)),
    user_agent: ctx.req.headers['user-agent'] || null,
    accept_language: ctx.req.headers['accept-language'] || null,
  };
}

const QR_ECC = {
  L: [-1, 7, 10, 15, 20, 26, 18, 20, 24, 30, 18],
  M: [-1, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26],
  Q: [-1, 13, 22, 18, 26, 18, 24, 18, 22, 20, 24],
  H: [-1, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28],
};
const QR_BLOCKS = {
  L: [-1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4],
  M: [-1, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5],
  Q: [-1, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8],
  H: [-1, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8],
};
const QR_FORMAT = { L: 1, M: 0, Q: 3, H: 2 };
const QR_MAX_VER = 10;

const qrRawModules = (ver) => {
  let r = (16 * ver + 128) * ver + 64;
  if (ver >= 2) {
    const n = Math.floor(ver / 7) + 2;
    r -= (25 * n - 10) * n - 55;
    if (ver >= 7) r -= 36;
  }
  return r;
};
const qrDataCodewords = (ver, ecl) => Math.floor(qrRawModules(ver) / 8) - QR_ECC[ecl][ver] * QR_BLOCKS[ecl][ver];
const qrCapacity = (ecl) => Math.floor((qrDataCodewords(QR_MAX_VER, ecl) * 8 - 4 - 16) / 8);

function gfMul(x, y) {
  let z = 0;
  for (let i = 7; i >= 0; i--) {
    z = (z << 1) ^ ((z >>> 7) * 0x11d);
    z ^= ((y >>> i) & 1) * x;
  }
  return z;
}
function rsDivisor(degree) {
  const result = new Array(degree).fill(0);
  result[degree - 1] = 1;
  let root = 1;
  for (let i = 0; i < degree; i++) {
    for (let j = 0; j < result.length; j++) {
      result[j] = gfMul(result[j], root);
      if (j + 1 < result.length) result[j] ^= result[j + 1];
    }
    root = gfMul(root, 2);
  }
  return result;
}
function rsRemainder(data, divisor) {
  const result = divisor.map(() => 0);
  for (const b of data) {
    const factor = b ^ result.shift();
    result.push(0);
    divisor.forEach((coef, i) => { result[i] ^= gfMul(coef, factor); });
  }
  return result;
}

function qrAlignPositions(ver) {
  if (ver === 1) return [];
  const n = Math.floor(ver / 7) + 2;
  const step = Math.ceil((ver * 4 + 4) / (n * 2 - 2)) * 2;
  const res = [6];
  for (let i = 0, pos = ver * 4 + 10; i < n - 1; i++, pos -= step) res.splice(1, 0, pos);
  return res;
}

function qrEncode(text, ecl) {
  const data = Buffer.from(text, 'utf8');
  let ver = 1;
  for (; ver <= QR_MAX_VER; ver++) {
    if (4 + (ver < 10 ? 8 : 16) + data.length * 8 <= qrDataCodewords(ver, ecl) * 8) break;
  }
  if (ver > QR_MAX_VER) throw fail(400, `Metin çok uzun (${ecl} düzeyinde en fazla ${qrCapacity(ecl)} bayt)`);

  const bits = [];
  const put = (v, n) => { for (let i = n - 1; i >= 0; i--) bits.push((v >>> i) & 1); };
  const cap = qrDataCodewords(ver, ecl) * 8;
  put(4, 4);
  put(data.length, ver < 10 ? 8 : 16);
  for (const b of data) put(b, 8);
  put(0, Math.min(4, cap - bits.length));
  put(0, (8 - (bits.length % 8)) % 8);
  for (let pad = 0xec; bits.length < cap; pad ^= 0xec ^ 0x11) put(pad, 8);
  const cw = [];
  for (let i = 0; i < bits.length; i += 8) {
    let v = 0;
    for (let j = 0; j < 8; j++) v = (v << 1) | bits[i + j];
    cw.push(v);
  }

  const numBlocks = QR_BLOCKS[ecl][ver], eccLen = QR_ECC[ecl][ver];
  const rawCw = Math.floor(qrRawModules(ver) / 8);
  const numShort = numBlocks - (rawCw % numBlocks), shortLen = Math.floor(rawCw / numBlocks);
  const div = rsDivisor(eccLen);
  const blocks = [];
  for (let i = 0, k = 0; i < numBlocks; i++) {
    const dat = cw.slice(k, k + shortLen - eccLen + (i < numShort ? 0 : 1));
    k += dat.length;
    const ecc = rsRemainder(dat, div);
    if (i < numShort) dat.push(0);
    blocks.push(dat.concat(ecc));
  }
  const all = [];
  for (let i = 0; i < blocks[0].length; i++) {
    blocks.forEach((blk, j) => { if (i !== shortLen - eccLen || j >= numShort) all.push(blk[i]); });
  }

  const size = ver * 4 + 17;
  const mod = Array.from({ length: size }, () => new Array(size).fill(false));
  const isFn = Array.from({ length: size }, () => new Array(size).fill(false));
  const setFn = (x, y, dark) => { mod[y][x] = dark; isFn[y][x] = true; };

  for (let i = 0; i < size; i++) { setFn(6, i, i % 2 === 0); setFn(i, 6, i % 2 === 0); }
  const finder = (cx, cy) => {
    for (let dy = -4; dy <= 4; dy++) for (let dx = -4; dx <= 4; dx++) {
      const dist = Math.max(Math.abs(dx), Math.abs(dy)), x = cx + dx, y = cy + dy;
      if (x >= 0 && x < size && y >= 0 && y < size) setFn(x, y, dist !== 2 && dist !== 4);
    }
  };
  finder(3, 3); finder(size - 4, 3); finder(3, size - 4);
  const ap = qrAlignPositions(ver), n = ap.length;
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    if ((i === 0 && j === 0) || (i === 0 && j === n - 1) || (i === n - 1 && j === 0)) continue;
    for (let dy = -2; dy <= 2; dy++) for (let dx = -2; dx <= 2; dx++) setFn(ap[i] + dx, ap[j] + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
  }

  const drawFormat = (mask) => {
    const d = (QR_FORMAT[ecl] << 3) | mask;
    let rem = d;
    for (let i = 0; i < 10; i++) rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
    const fb = ((d << 10) | rem) ^ 0x5412;
    const bit = (i) => ((fb >>> i) & 1) !== 0;
    for (let i = 0; i <= 5; i++) setFn(8, i, bit(i));
    setFn(8, 7, bit(6)); setFn(8, 8, bit(7)); setFn(7, 8, bit(8));
    for (let i = 9; i < 15; i++) setFn(14 - i, 8, bit(i));
    for (let i = 0; i < 8; i++) setFn(size - 1 - i, 8, bit(i));
    for (let i = 8; i < 15; i++) setFn(8, size - 15 + i, bit(i));
    setFn(8, size - 8, true);
  };
  drawFormat(0);

  if (ver >= 7) {
    let rem = ver;
    for (let i = 0; i < 12; i++) rem = (rem << 1) ^ ((rem >>> 11) * 0x1f25);
    const vb = (ver << 12) | rem;
    for (let i = 0; i < 18; i++) {
      const c = ((vb >>> i) & 1) !== 0, a = size - 11 + (i % 3), b = Math.floor(i / 3);
      setFn(a, b, c); setFn(b, a, c);
    }
  }

  let idx = 0;
  for (let right = size - 1; right >= 1; right -= 2) {
    if (right === 6) right = 5;
    for (let vert = 0; vert < size; vert++) for (let j = 0; j < 2; j++) {
      const x = right - j, upward = ((right + 1) & 2) === 0, y = upward ? size - 1 - vert : vert;
      if (!isFn[y][x] && idx < all.length * 8) {
        mod[y][x] = ((all[idx >>> 3] >>> (7 - (idx & 7))) & 1) !== 0;
        idx++;
      }
    }
  }

  const applyMask = (mask) => {
    for (let y = 0; y < size; y++) for (let x = 0; x < size; x++) {
      if (isFn[y][x]) continue;
      let inv;
      switch (mask) {
        case 0: inv = (x + y) % 2 === 0; break;
        case 1: inv = y % 2 === 0; break;
        case 2: inv = x % 3 === 0; break;
        case 3: inv = (x + y) % 3 === 0; break;
        case 4: inv = (Math.floor(x / 3) + Math.floor(y / 2)) % 2 === 0; break;
        case 5: inv = ((x * y) % 2) + ((x * y) % 3) === 0; break;
        case 6: inv = (((x * y) % 2) + ((x * y) % 3)) % 2 === 0; break;
        default: inv = (((x + y) % 2) + ((x * y) % 3)) % 2 === 0;
      }
      if (inv) mod[y][x] = !mod[y][x];
    }
  };
  const penalty = () => {
    let r = 0;
    const lines = [];
    for (let y = 0; y < size; y++) lines.push(mod[y]);
    for (let x = 0; x < size; x++) lines.push(mod.map((row) => row[x]));
    for (const line of lines) {
      let run = 1;
      for (let i = 1; i < size; i++) {
        if (line[i] === line[i - 1]) { run++; if (run === 5) r += 3; else if (run > 5) r++; } else run = 1;
      }
      const str = line.map((b) => (b ? '1' : '0')).join('');
      for (const pat of ['10111010000', '00001011101']) {
        for (let p = str.indexOf(pat); p !== -1; p = str.indexOf(pat, p + 1)) r += 40;
      }
    }
    for (let y = 0; y < size - 1; y++) for (let x = 0; x < size - 1; x++) {
      if (mod[y][x] === mod[y][x + 1] && mod[y][x] === mod[y + 1][x] && mod[y][x] === mod[y + 1][x + 1]) r += 3;
    }
    const dark = mod.reduce((s, row) => s + row.filter(Boolean).length, 0);
    r += (Math.ceil(Math.abs(dark * 20 - size * size * 10) / (size * size)) - 1) * 10;
    return r;
  };
  let best = 0, bestScore = Infinity;
  for (let m = 0; m < 8; m++) {
    applyMask(m); drawFormat(m);
    const p = penalty();
    if (p < bestScore) { bestScore = p; best = m; }
    applyMask(m);
  }
  applyMask(best);
  drawFormat(best);
  return { modules: mod, version: ver };
}

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();
const crc32 = (buf) => {
  let c = 0xffffffff;
  for (const b of buf) c = CRC_TABLE[(c ^ b) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
};
function pngChunk(type, data) {
  const len = Buffer.alloc(4); len.writeUInt32BE(data.length);
  const td = Buffer.concat([Buffer.from(type, 'ascii'), data]);
  const crc = Buffer.alloc(4); crc.writeUInt32BE(crc32(td));
  return Buffer.concat([len, td, crc]);
}
function qrPng(mod, scale, margin) {
  const n = mod.length, size = (n + margin * 2) * scale;
  const raw = Buffer.alloc((1 + size) * size, 255);
  for (let y = 0; y < size; y++) {
    const my = Math.floor(y / scale) - margin, off = y * (1 + size);
    raw[off] = 0;
    for (let x = 0; x < size; x++) {
      const mx = Math.floor(x / scale) - margin;
      if (my >= 0 && my < n && mx >= 0 && mx < n && mod[my][mx]) raw[off + 1 + x] = 0;
    }
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(size, 0); ihdr.writeUInt32BE(size, 4); ihdr[8] = 8;
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), pngChunk('IHDR', ihdr), pngChunk('IDAT', zlib.deflateSync(raw)), pngChunk('IEND', Buffer.alloc(0))]);
}
function qrSvg(mod, scale, margin) {
  const n = mod.length, tot = n + margin * 2;
  let d = '';
  for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) if (mod[y][x]) d += `M${x + margin} ${y + margin}h1v1h-1z`;
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${tot} ${tot}" width="${tot * scale}" height="${tot * scale}" shape-rendering="crispEdges"><rect width="${tot}" height="${tot}" fill="#fff"/><path d="${d}" fill="#000"/></svg>\n`;
}
function qrTerminal(mod, margin, invert) {
  const n = mod.length, tot = n + margin * 2;
  const get = (x, y) => { const mx = x - margin, my = y - margin; return mx >= 0 && my >= 0 && mx < n && my < n && mod[my][mx]; };
  const lines = [];
  for (let y = 0; y < tot; y += 2) {
    let line = '';
    for (let x = 0; x < tot; x++) {
      const top = get(x, y) !== invert, bot = get(x, y + 1) !== invert;
      line += top && bot ? '█' : top ? '▀' : bot ? '▄' : ' ';
    }
    lines.push(line);
  }
  return lines.join('\n') + '\n';
}

function qrRoute(_, ctx) {
  const text = textArg(ctx, ctx.rest);
  const ecl = (ctx.q('ecc') || 'M').toUpperCase();
  if (!QR_ECC[ecl]) throw fail(400, 'ecc değeri L, M, Q veya H olmalı');
  const format = (ctx.q('format') || 'png').toLowerCase();
  if (!['png', 'svg', 'text'].includes(format)) throw fail(400, 'format değeri png, svg veya text olmalı');
  const scale = clamp(int(ctx.q('scale'), 8), 1, 20);
  const margin = clamp(int(ctx.q('margin'), 4), 0, 10);
  const { modules } = qrEncode(text, ecl);
  if (format === 'svg') return { __raw: true, type: 'image/svg+xml; charset=utf-8', body: qrSvg(modules, scale, margin) };
  if (format === 'text') return { __raw: true, type: 'text/plain; charset=utf-8', body: qrTerminal(modules, margin, ctx.q('invert') !== '0') };
  return { __raw: true, type: 'image/png', body: qrPng(modules, scale, margin) };
}

const emailSessions = new Map();
const jsonResult = (body, status = 200) => ({ __json: true, status, body });
const escapeXml = (value) => String(value).replace(/[<>&"']/g, (c) => ({ '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;', "'": '&apos;' })[c]);

function fetchLogoData(url) {
  return new Promise((resolve, reject) => {
    const req = https.request(url, {
      method: 'GET',
      lookup: safeLookup,
      agent: false,
      timeout: 8000,
      headers: { 'user-agent': 'DomainIpAPI/1.0', accept: 'image/png,image/jpeg,image/gif,image/webp' },
    }, (res) => {
      if (res.statusCode !== 200) {
        res.resume();
        return reject(fail(502, 'Logo görseli alınamadı veya yönlendirme döndü'));
      }
      const type = String(res.headers['content-type'] || '').split(';')[0].trim().toLowerCase();
      if (!['image/png', 'image/jpeg', 'image/gif', 'image/webp'].includes(type)) {
        res.resume();
        return reject(fail(400, 'Logo PNG, JPEG, GIF veya WebP olmalı'));
      }
      const chunks = [];
      let size = 0;
      res.on('data', (chunk) => {
        size += chunk.length;
        if (size > 2 * 1024 * 1024) {
          req.destroy();
          reject(fail(413, 'Logo görseli en fazla 2 MB olabilir'));
        } else {
          chunks.push(chunk);
        }
      });
      res.on('end', () => resolve(`data:${type};base64,${Buffer.concat(chunks).toString('base64')}`));
      res.on('error', () => reject(fail(502, 'Logo görseli okunamadı')));
    });
    req.on('timeout', () => req.destroy(fail(502, 'Logo görseli isteği zaman aşımına uğradı')));
    req.on('error', () => reject(fail(502, 'Logo görseli alınamadı')));
    req.end();
  });
}

async function qrCustomRoute(_, ctx) {
  const text = ctx.q('text') ?? ctx.q('q') ?? '';
  if (!text) throw fail(400, 'Kullanım: /qrcode/custom?text=...&logo=https%3A%2F%2F...');
  if (text.length > MAX_TEXT) throw fail(400, `Metin çok uzun (en fazla ${MAX_TEXT} karakter)`);
  const logo = ctx.q('logo') || '';
  const ecc = (ctx.q('ecc') || 'H').toUpperCase();
  if (!QR_ECC[ecc]) throw fail(400, 'ecc değeri L, M, Q veya H olmalı');
  const scale = clamp(int(ctx.q('scale'), 8), 1, 20);
  const margin = clamp(int(ctx.q('margin'), 4), 2, 10);
  const { modules } = qrEncode(text, ecc);
  let svg = qrSvg(modules, scale, margin);
  if (logo) {
    const total = modules.length + margin * 2;
    const box = Math.max(7, Math.floor(modules.length * 0.22));
    const at = (total - box) / 2;
    let overlay;
    let url = null;
    try { url = new URL(logo); } catch {}
    if (url) {
      if (url.protocol !== 'https:' || !url.hostname || url.username || url.password || (url.port && url.port !== '443')) throw fail(400, 'Logo bağlantısı HTTPS/443 olmalı');
      let addresses;
      try { addresses = await dns.lookup(url.hostname, { all: true }); } catch { throw fail(400, 'Logo alan adı çözümlenemedi'); }
      if (!addresses.length || addresses.some((item) => isPrivateIp(item.address))) throw fail(400, 'Logo bağlantısında özel veya yerel adres kullanılamaz');
      const data = await fetchLogoData(url);
      overlay = `<image x="${at}" y="${at}" width="${box}" height="${box}" href="${data}" preserveAspectRatio="xMidYMid meet"/>`;
    } else {
      const label = [...logo].slice(0, 8).join('');
      overlay = `<text x="${total / 2}" y="${total / 2 + box * 0.17}" text-anchor="middle" font-size="${box * 0.7}" font-family="sans-serif">${escapeXml(label)}</text>`;
    }
    svg = svg.replace('</svg>', `<rect x="${at - 0.5}" y="${at - 0.5}" width="${box + 1}" height="${box + 1}" rx="1" fill="#fff"/>${overlay}</svg>`);
  }
  return { __raw: true, type: 'image/svg+xml; charset=utf-8', body: svg };
}

function parseColor(input) {
  const raw = String(input || '').trim().replace(/^#/, '');
  if (!/^(?:[0-9a-f]{3,4}|[0-9a-f]{6}|[0-9a-f]{8})$/i.test(raw)) throw fail(400, 'HEX renk kodu 3, 4, 6 veya 8 haneli olmalı');
  const full = raw.length <= 4 ? [...raw].map((c) => c + c).join('') : raw;
  const r = Number.parseInt(full.slice(0, 2), 16);
  const g = Number.parseInt(full.slice(2, 4), 16);
  const b = Number.parseInt(full.slice(4, 6), 16);
  const a = full.length === 8 ? Number.parseInt(full.slice(6, 8), 16) / 255 : 1;
  const rn = r / 255, gn = g / 255, bn = b / 255;
  const max = Math.max(rn, gn, bn), min = Math.min(rn, gn, bn);
  const delta = max - min;
  let h = 0;
  if (delta) {
    if (max === rn) h = 60 * (((gn - bn) / delta) % 6);
    else if (max === gn) h = 60 * ((bn - rn) / delta + 2);
    else h = 60 * ((rn - gn) / delta + 4);
  }
  if (h < 0) h += 360;
  const l = (max + min) / 2;
  const s = delta ? delta / (1 - Math.abs(2 * l - 1)) : 0;
  return {
    hex: `#${[r, g, b].map((x) => x.toString(16).padStart(2, '0')).join('')}${a < 1 ? Math.round(a * 255).toString(16).padStart(2, '0') : ''}`,
    rgb: { r, g, b },
    hsl: { h: Math.round(h), s: Math.round(s * 100), l: Math.round(l * 100) },
    alpha: Number(a.toFixed(3)),
  };
}

function colorRoute(_, ctx) {
  const input = ctx.rest.join('/') || ctx.q('hex') || ctx.q('color') || '';
  const color = parseColor(input);
  if ((ctx.q('format') || '').toLowerCase() !== 'svg') return jsonResult(color);
  const { r, g, b } = color.rgb;
  const alpha = color.alpha;
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="640" height="360"><rect width="100%" height="100%" fill="rgb(${r},${g},${b})" fill-opacity="${alpha}"/><rect x="24" y="24" width="592" height="312" rx="24" fill="none" stroke="#111" stroke-opacity=".18"/><text x="48" y="292" font-family="Arial,sans-serif" font-size="36" font-weight="700" fill="${r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#111' : '#fff'}">${escapeXml(color.hex)}</text><text x="48" y="326" font-family="Arial,sans-serif" font-size="18" fill="${r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#111' : '#fff'}">RGB ${r}, ${g}, ${b} · HSL ${color.hsl.h}°, ${color.hsl.s}%, ${color.hsl.l}%</text></svg>`;
  return { __raw: true, type: 'image/svg+xml; charset=utf-8', body: svg };
}

function rollRoute(_, ctx) {
  const input = (ctx.rest.join('/') || ctx.q('dice') || '1d6').toLowerCase();
  const match = input.match(/^(\d{1,3})d(\d{1,6})$/);
  if (!match) throw fail(400, 'Kullanım: /roll/2d6 (en fazla 100 zar, zar başına 100000 yüz)');
  const count = Number(match[1]), sides = Number(match[2]);
  if (count < 1 || count > 100 || sides < 2 || sides > 100000) throw fail(400, 'Zar sayısı 1-100, yüz sayısı 2-100000 arasında olmalı');
  const rolls = Array.from({ length: count }, () => crypto.randomInt(1, sides + 1));
  return { expression: `${count}d${sides}`, rolls, total: rolls.reduce((sum, n) => sum + n, 0) };
}

function flipRoute(_, ctx) {
  const count = clamp(int(ctx.q('count') || ctx.rest[0], 1), 1, 100);
  const results = Array.from({ length: count }, () => crypto.randomInt(0, 2) ? 'yazı' : 'tura');
  return { count, results, yazı: results.filter((x) => x === 'yazı').length, tura: results.filter((x) => x === 'tura').length };
}

async function minecraftRoute(_, ctx) {
  const input = (ctx.rest.join('/') || ctx.q('server') || '').trim();
  if (!input || input.length > 253 || /[/?#@\s]/.test(input)) throw fail(400, 'Kullanım: /minecraft/{sunucu[:port]}');
  let host = input, port = '';
  const bracketed = input.match(/^\[([0-9a-f:.]+)\](?::(\d{1,5}))?$/i);
  const plain = !bracketed ? input.match(/^([^:]+):(\d{1,5})$/) : null;
  if (bracketed) {
    host = `[${bracketed[1]}]`;
    if (bracketed[2]) port = `:${bracketed[2]}`;
  } else if (plain) {
    host = plain[1];
    port = `:${plain[2]}`;
  }
  if (port && (+port.slice(1) < 1 || +port.slice(1) > 65535)) throw fail(400, 'Port 1-65535 arasında olmalı');
  const ipCandidate = host.replace(/^\[|\]$/g, '');
  if (!net.isIP(ipCandidate) && !cleanDomain(host)) throw fail(400, 'Geçersiz Minecraft sunucu adresi');
  const data = await fetchJson(`https://api.mcsrvstat.us/3/${encodeURIComponent(input)}`, {}, 'Minecraft durum servisine ulaşılamadı');
  return {
    server: `${host}${port}`,
    online: !!data.online,
    players: data.players ? { online: data.players.online ?? 0, max: data.players.max ?? null, sample: data.players.list || [] } : { online: 0, max: null, sample: [] },
    motd: data.motd?.clean || data.motd?.raw || [],
    version: data.version || null,
    software: data.software || null,
    hostname: data.hostname || null,
    port: data.port || (port ? Number(port.slice(1)) : 25565),
  };
}

async function lyricsRoute(_, ctx) {
  const query = ctx.q('q') || ctx.q('track') || ctx.rest.join('/');
  if (!query) throw fail(400, 'Kullanım: /lyrics?q=şarkı%20adı');
  if (query.length > 200) throw fail(400, 'Arama en fazla 200 karakter olabilir');
  const data = await fetchJson(`https://lrclib.net/api/search?q=${encodeURIComponent(query)}`, { headers: { 'user-agent': 'DomainIpAPI/1.0' } }, 'Şarkı sözleri servisine ulaşılamadı');
  const tracks = Array.isArray(data) ? data.slice(0, 10).map((item) => ({
    title: item.trackName || null,
    artist: item.artistName || null,
    album: item.albumName || null,
    duration: item.duration || null,
    instrumental: !!item.instrumental,
    lyrics: item.plainLyrics || item.syncedLyrics || null,
    synced_lyrics: item.syncedLyrics || null,
  })) : [];
  return jsonResult({ query, count: tracks.length, tracks });
}

async function screenshotRoute(_, ctx) {
  const input = ctx.q('url') || ctx.rest.join('/');
  if (!input) throw fail(400, 'Kullanım: /screenshot?url=https%3A%2F%2Fexample.com');
  const result = await trace(input, 5);
  if (!result.final || result.final.status < 200 || result.final.status >= 400) throw fail(400, 'Ekran görüntüsü alınacak sayfaya erişilemiyor');
  const target = new URL(result.final.url);
  let addresses;
  try { addresses = await dns.lookup(target.hostname, { all: true }); } catch { throw fail(400, 'Alan adı çözümlenemedi'); }
  if (!addresses.length || addresses.some((item) => isPrivateIp(item.address))) throw fail(400, 'Özel veya yerel adreslere erişim engellendi');
  let response;
  try {
    response = await fetch(`https://image.thum.io/get/width/1200/crop/900/noanimate/${result.final.url}`, { signal: AbortSignal.timeout(30000) });
  } catch { throw fail(502, 'Ekran görüntüsü servisine ulaşılamadı'); }
  if (!response.ok) throw fail(502, `Ekran görüntüsü servisi hata verdi (${response.status})`);
  const type = response.headers.get('content-type') || 'image/png';
  if (!type.startsWith('image/')) throw fail(502, 'Ekran görüntüsü servisi görsel döndürmedi');
  const body = Buffer.from(await response.arrayBuffer());
  if (body.length > 8 * 1024 * 1024) throw fail(502, 'Ekran görüntüsü dosyası çok büyük');
  return { __raw: true, type, body };
}

async function tempmailRoute(_, ctx) {
  const action = ctx.rest[0] || 'new';
  if (action === 'new') {
    if (ctx.req.method !== 'POST') throw fail(405, 'Yeni geçici e-posta oluşturmak için POST /tempmail/new kullanın');
    let domains;
    try { domains = await fetchJson('https://api.mail.tm/domains?page=1', {}, 'Geçici e-posta servisine ulaşılamadı'); } catch (e) { throw e; }
    const domain = domains['hydra:member']?.find((item) => item.isActive && !item.isPrivate)?.domain;
    if (!domain) throw fail(502, 'Kullanılabilir geçici e-posta alan adı bulunamadı');
    const address = `${crypto.randomBytes(10).toString('hex')}@${domain}`;
    const password = crypto.randomBytes(32).toString('base64url');
    const account = await fetchJson('https://api.mail.tm/accounts', {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ address, password }),
    }, 'Geçici e-posta hesabı oluşturulamadı');
    const auth = await fetchJson('https://api.mail.tm/token', {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ address, password }),
    }, 'Geçici e-posta oturumu açılamadı');
    const id = crypto.randomBytes(24).toString('base64url');
    emailSessions.set(id, { token: auth.token, address: account.address || address, expires: Date.now() + 4 * 60 * 60 * 1000 });
    return jsonResult({ id, address: account.address || address, expires_in_seconds: 14400, inbox: `/tempmail/inbox/${id}` }, 201);
  }
  if (action !== 'inbox' || !ctx.rest[1]) throw fail(400, 'Kullanım: /tempmail/new veya /tempmail/inbox/{id}');
  const id = ctx.rest[1];
  const session = emailSessions.get(id);
  if (!session || session.expires <= Date.now()) {
    emailSessions.delete(id);
    throw fail(404, 'E-posta oturumu bulunamadı veya süresi doldu');
  }
  const messages = await fetchJson('https://api.mail.tm/messages?page=1', { headers: { authorization: `Bearer ${session.token}` } }, 'Gelen kutusu alınamadı');
  return jsonResult({
    address: session.address,
    count: messages['hydra:member']?.length || 0,
    messages: (messages['hydra:member'] || []).map((item) => ({
      id: item.id,
      from: item.from?.address || null,
      subject: item.subject || '',
      intro: item.intro || '',
      created_at: item.createdAt || null,
      seen: !!item.seen,
    })),
  });
}

async function fetchJson(url, options, message) {
  let response;
  try { response = await fetch(url, { ...options, signal: AbortSignal.timeout(12000) }); } catch { throw fail(502, message); }
  let data;
  try { data = await response.json(); } catch { data = null; }
  if (!response.ok) {
    const status = response.status === 429 ? 503 : 502;
    throw fail(status, data?.detail || data?.message || message);
  }
  return data;
}

const domainRoute = (run, extra = {}) => ({ param: 'domain', clean: cleanDomain, bad: 'Geçersiz alan adı', run, cache: true, ...extra });
const anyRoute = (run, extra = {}) => ({ param: 'deger', clean: (x) => x, run, ...extra });
const customRoute = (run) => ({ custom: true, run });

// ---------------------------------------------------------------------------
// Günlük hayat endpoint'leri: hava, döviz, deprem, vikipedi, hesaplamalar...
// ---------------------------------------------------------------------------
const EVERYDAY = (() => {
  const UA = { 'user-agent': 'DomainIpAPI/1.0 (+https://discord.gg/apitr)' };
  const DAYS = ['Pazar', 'Pazartesi', 'Salı', 'Çarşamba', 'Perşembe', 'Cuma', 'Cumartesi'];
  const MONTHS = ['Ocak', 'Şubat', 'Mart', 'Nisan', 'Mayıs', 'Haziran', 'Temmuz', 'Ağustos', 'Eylül', 'Ekim', 'Kasım', 'Aralık'];
  const round = (n, d = 1) => (typeof n === 'number' && Number.isFinite(n) ? Math.round(n * 10 ** d) / 10 ** d : null);
  const sig = (n) => (Number.isFinite(n) ? Number(n.toPrecision(10)) : null);
  const pad = (n) => String(n).padStart(2, '0');
  const isoMs = (ms) => new Date(ms).toISOString().slice(0, 10);
  const trTime = (ms) => new Date(ms + 3 * 36e5).toISOString().slice(0, 19).replace('T', ' ');
  const trNow = () => { const d = new Date(Date.now() + 3 * 36e5); return { y: d.getUTCFullYear(), m: d.getUTCMonth() + 1, d: d.getUTCDate() }; };
  const trToday = () => { const t = trNow(); return Date.UTC(t.y, t.m - 1, t.d); };
  const norm = (s) => String(s ?? '').toLocaleLowerCase('tr').replace(/ç/g, 'c').replace(/ğ/g, 'g').replace(/ı/g, 'i').replace(/ö/g, 'o').replace(/ş/g, 's').replace(/ü/g, 'u').replace(/\s+/g, ' ').trim();

  async function memo(key, ttl, run) {
    const hit = cache.get(key);
    if (hit && Date.now() - hit.at < ttl) return { ...hit.data, cached: true };
    const data = await run();
    cache.set(key, { at: Date.now(), data });
    return { ...data, cached: false };
  }

  const seg = (ctx, i) => (ctx.rest[i] === undefined ? '' : dec(ctx.rest[i]).trim());
  const pathOrQuery = (ctx, i, ...names) => seg(ctx, i) || names.map((n) => (ctx.q(n) || '').trim()).find(Boolean) || '';

  function num(raw, what) {
    let s = String(raw ?? '').trim().replace(/\s/g, '');
    if (!s) throw fail(400, `${what} gerekli`);
    if (s.includes(',') && s.includes('.')) s = s.replace(/\./g, '').replace(',', '.');
    else if (s.includes(',')) s = s.replace(',', '.');
    const n = Number(s);
    if (!Number.isFinite(n)) throw fail(400, `${what} geçerli bir sayı olmalı`);
    return n;
  }

  function parseDate(raw, what = 'Tarih') {
    const s = String(raw || '').trim();
    let m = s.match(/^(\d{4})-(\d{1,2})-(\d{1,2})$/);
    let y, mo, d;
    if (m) [y, mo, d] = [+m[1], +m[2], +m[3]];
    else if ((m = s.match(/^(\d{1,2})\.(\d{1,2})\.(\d{4})$/))) [d, mo, y] = [+m[1], +m[2], +m[3]];
    else throw fail(400, `${what} YYYY-AA-GG biçiminde olmalı (örn. 1995-03-25)`);
    const ms = Date.UTC(y, mo - 1, d);
    const dt = new Date(ms);
    if (dt.getUTCFullYear() !== y || dt.getUTCMonth() !== mo - 1 || dt.getUTCDate() !== d) throw fail(400, `Geçersiz ${what.toLowerCase()}`);
    if (y < 1900 || y > 2200) throw fail(400, 'Yıl 1900-2200 arasında olmalı');
    return { y, m: mo, d, ms };
  }

  // ----------------------------- HAVA ---------------------------------------
  const WMO = {
    0: 'Açık', 1: 'Çoğunlukla açık', 2: 'Parçalı bulutlu', 3: 'Kapalı', 45: 'Sisli', 48: 'Kırağılı sis',
    51: 'Hafif çise', 53: 'Orta şiddetli çise', 55: 'Yoğun çise', 56: 'Dondurucu çise', 57: 'Yoğun dondurucu çise',
    61: 'Hafif yağmur', 63: 'Orta şiddetli yağmur', 65: 'Kuvvetli yağmur', 66: 'Dondurucu yağmur', 67: 'Kuvvetli dondurucu yağmur',
    71: 'Hafif kar', 73: 'Orta şiddetli kar', 75: 'Yoğun kar', 77: 'Kar taneleri',
    80: 'Hafif sağanak', 81: 'Orta şiddetli sağanak', 82: 'Şiddetli sağanak', 85: 'Hafif kar sağanağı', 86: 'Yoğun kar sağanağı',
    95: 'Gök gürültülü fırtına', 96: 'Dolu ile fırtına', 99: 'Şiddetli dolu ile fırtına',
  };
  const COMPASS = ['Kuzey', 'Kuzeydoğu', 'Doğu', 'Güneydoğu', 'Güney', 'Güneybatı', 'Batı', 'Kuzeybatı'];
  const compass = (deg) => (typeof deg === 'number' ? COMPASS[Math.round(deg / 45) % 8] : null);

  function cityArg(ctx, route) {
    const v = (ctx.rest.length ? ctx.rest.map(dec).join('/') : (ctx.q('q') || ctx.q('sehir') || '')).trim();
    if (!v) throw fail(400, `Kullanım: /${route}/{şehir}`);
    if (v.length > 100) throw fail(400, 'Şehir adı en fazla 100 karakter olabilir');
    return v;
  }
  function countryArg(ctx) {
    const c = (ctx.q('ulke') || '').trim().toUpperCase();
    if (c && !/^[A-Z]{2}$/.test(c)) throw fail(400, 'ulke iki harfli ülke kodu olmalı (örn. TR, DE)');
    return c;
  }

  async function geocode(name, country) {
    const key = `geo:${name.toLowerCase()}:${country}`;
    const hit = cache.get(key);
    if (hit && Date.now() - hit.at < 864e5) return hit.data;
    const data = await fetchJson(`https://geocoding-api.open-meteo.com/v1/search?name=${encodeURIComponent(name)}&count=10&language=tr&format=json`, { headers: UA }, 'Konum servisine ulaşılamadı');
    let list = data?.results || [];
    if (country) list = list.filter((r) => (r.country_code || '').toUpperCase() === country);
    const place = (!country && list.find((r) => r.country_code === 'TR')) || list[0];
    if (!place) throw fail(404, 'Konum bulunamadı');
    const out = {
      ad: place.name,
      bolge: place.admin1 || null,
      ulke: place.country || null,
      ulke_kodu: place.country_code || null,
      enlem: place.latitude,
      boylam: place.longitude,
      saat_dilimi: place.timezone || null,
    };
    cache.set(key, { at: Date.now(), data: out });
    return out;
  }

  async function hava(_, ctx) {
    const name = cityArg(ctx, 'hava');
    const country = countryArg(ctx);
    return memo(`hava:${name.toLowerCase()}:${country}`, 10 * 60e3, async () => {
      const g = await geocode(name, country);
      const f = await fetchJson(
        `https://api.open-meteo.com/v1/forecast?latitude=${g.enlem}&longitude=${g.boylam}` +
        '&current=temperature_2m,apparent_temperature,relative_humidity_2m,precipitation,weather_code,wind_speed_10m,wind_direction_10m,surface_pressure,is_day' +
        '&daily=weather_code,temperature_2m_max,temperature_2m_min,precipitation_sum,precipitation_probability_max,wind_speed_10m_max' +
        '&timezone=auto&forecast_days=5&wind_speed_unit=kmh',
        { headers: UA }, 'Hava durumu servisine ulaşılamadı');
      const c = f.current || {}, d = f.daily || {};
      return {
        konum: g,
        simdi: {
          durum: WMO[c.weather_code] || null,
          sicaklik_c: round(c.temperature_2m),
          hissedilen_c: round(c.apparent_temperature),
          nem_yuzde: round(c.relative_humidity_2m, 0),
          ruzgar_kmh: round(c.wind_speed_10m),
          ruzgar_yonu: compass(c.wind_direction_10m),
          basinc_hpa: round(c.surface_pressure, 0),
          yagis_mm: round(c.precipitation),
          gunduz: c.is_day === undefined ? null : !!c.is_day,
          olcum_zamani: c.time || null,
        },
        tahmin: (d.time || []).map((date, i) => ({
          tarih: date,
          gun: DAYS[new Date(`${date}T00:00:00Z`).getUTCDay()],
          durum: WMO[d.weather_code?.[i]] || null,
          en_dusuk_c: round(d.temperature_2m_min?.[i]),
          en_yuksek_c: round(d.temperature_2m_max?.[i]),
          yagis_mm: round(d.precipitation_sum?.[i]),
          yagis_ihtimali_yuzde: round(d.precipitation_probability_max?.[i], 0),
          maks_ruzgar_kmh: round(d.wind_speed_10m_max?.[i]),
        })),
        kaynak: 'Open-Meteo',
      };
    });
  }

  const euAqi = (v) => (v == null ? null : v <= 20 ? 'Çok iyi' : v <= 40 ? 'İyi' : v <= 60 ? 'Orta' : v <= 80 ? 'Kötü' : v <= 100 ? 'Çok kötü' : 'Aşırı kötü');
  const usAqi = (v) => (v == null ? null : v <= 50 ? 'İyi' : v <= 100 ? 'Orta' : v <= 150 ? 'Hassas gruplar için sağlıksız' : v <= 200 ? 'Sağlıksız' : v <= 300 ? 'Çok sağlıksız' : 'Tehlikeli');

  async function havaKalitesi(_, ctx) {
    const name = cityArg(ctx, 'havakalitesi');
    const country = countryArg(ctx);
    return memo(`aqi:${name.toLowerCase()}:${country}`, 30 * 60e3, async () => {
      const g = await geocode(name, country);
      const a = await fetchJson(
        `https://air-quality-api.open-meteo.com/v1/air-quality?latitude=${g.enlem}&longitude=${g.boylam}` +
        '&current=european_aqi,us_aqi,pm10,pm2_5,carbon_monoxide,nitrogen_dioxide,sulphur_dioxide,ozone&timezone=auto',
        { headers: UA }, 'Hava kalitesi servisine ulaşılamadı');
      const c = a.current || {};
      return {
        konum: g,
        avrupa_aqi: round(c.european_aqi, 0),
        avrupa_seviye: euAqi(c.european_aqi),
        abd_aqi: round(c.us_aqi, 0),
        abd_seviye: usAqi(c.us_aqi),
        pm2_5_ugm3: round(c.pm2_5),
        pm10_ugm3: round(c.pm10),
        ozon_ugm3: round(c.ozone),
        no2_ugm3: round(c.nitrogen_dioxide),
        so2_ugm3: round(c.sulphur_dioxide),
        co_ugm3: round(c.carbon_monoxide, 0),
        olcum_zamani: c.time || null,
        kaynak: 'Open-Meteo / CAMS',
      };
    });
  }

  const uvLevel = (v) => (v == null ? null : v < 3 ? 'Düşük' : v < 6 ? 'Orta' : v < 8 ? 'Yüksek' : v < 11 ? 'Çok yüksek' : 'Aşırı');
  const dur = (sec) => (typeof sec === 'number' ? `${Math.floor(sec / 3600)} sa ${Math.round((sec % 3600) / 60)} dk` : null);

  async function gunes(_, ctx) {
    const name = cityArg(ctx, 'gunes');
    const country = countryArg(ctx);
    return memo(`gunes:${name.toLowerCase()}:${country}`, 60 * 60e3, async () => {
      const g = await geocode(name, country);
      const f = await fetchJson(
        `https://api.open-meteo.com/v1/forecast?latitude=${g.enlem}&longitude=${g.boylam}&daily=sunrise,sunset,daylight_duration,uv_index_max&timezone=auto&forecast_days=1`,
        { headers: UA }, 'Güneş verisi servisine ulaşılamadı');
      const d = f.daily || {};
      return {
        konum: g,
        tarih: d.time?.[0] || null,
        gun_dogumu: d.sunrise?.[0]?.slice(11) || null,
        gun_batimi: d.sunset?.[0]?.slice(11) || null,
        gun_uzunlugu: dur(d.daylight_duration?.[0]),
        uv_indeksi_maks: round(d.uv_index_max?.[0]),
        uv_seviyesi: uvLevel(d.uv_index_max?.[0]),
        kaynak: 'Open-Meteo',
      };
    });
  }

  // ----------------------------- AY EVRESİ ----------------------------------
  const SYN = 29.530588853;
  const NEW_MOON = Date.UTC(2000, 0, 6, 18, 14);
  const PHASES = [
    [1.84566, 'Yeni Ay'], [5.53699, 'Büyüyen Hilal'], [9.22831, 'İlk Dördün'], [12.91963, 'Büyüyen Şişkin Ay'],
    [16.61096, 'Dolunay'], [20.30228, 'Küçülen Şişkin Ay'], [23.99361, 'Son Dördün'], [27.68493, 'Küçülen Hilal'],
    [Infinity, 'Yeni Ay'],
  ];
  function ay(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'tarih');
    const base = raw ? parseDate(raw).ms + 12 * 36e5 : Date.now();
    const age = ((((base - NEW_MOON) / 864e5) % SYN) + SYN) % SYN;
    const [, name] = PHASES.find((p) => age < p[0]);
    const nextNew = base + (SYN - age) * 864e5;
    const nextFull = base + (age < SYN / 2 ? SYN / 2 - age : SYN * 1.5 - age) * 864e5;
    return {
      tarih: isoMs(base),
      evre: name,
      ay_yasi_gun: round(age),
      aydinlanma_yuzde: round(((1 - Math.cos((2 * Math.PI * age) / SYN)) / 2) * 100, 0),
      sonraki_yeni_ay: isoMs(nextNew),
      sonraki_dolunay: isoMs(nextFull),
      not: 'Ortalama ay döngüsüne göre yaklaşık hesaptır (±1 gün).',
    };
  }

  // ----------------------------- DÖVİZ (TCMB) -------------------------------
  async function tcmbRates() {
    const hit = cache.get('tcmb:today');
    if (hit && Date.now() - hit.at < 10 * 60e3) return hit.data;
    let xml;
    try {
      const r = await fetch('https://www.tcmb.gov.tr/kurlar/today.xml', { headers: UA, signal: AbortSignal.timeout(10000) });
      if (!r.ok) throw new Error(String(r.status));
      xml = await r.text();
    } catch { throw fail(502, 'TCMB kur servisine ulaşılamadı'); }
    const tarih = xml.match(/<Tarih_Date[^>]*\sTarih="([^"]+)"/)?.[1] || null;
    const rates = {};
    for (const m of xml.matchAll(/<Currency\b[^>]*\bKod="([A-Z]{3})"[^>]*>([\s\S]*?)<\/Currency>/g)) {
      const body = m[2];
      const unit = parseFloat(body.match(/<Unit>([^<]*)<\/Unit>/)?.[1]) || 1;
      const get = (t) => { const n = parseFloat(body.match(new RegExp(`<${t}>([^<]*)</${t}>`))?.[1]); return Number.isFinite(n) && n > 0 ? n / unit : null; };
      rates[m[1]] = {
        isim: body.match(/<Isim>([^<]*)<\/Isim>/)?.[1]?.trim() || m[1],
        alis: get('ForexBuying'),
        satis: get('ForexSelling'),
        efektif_alis: get('BanknoteBuying'),
        efektif_satis: get('BanknoteSelling'),
      };
    }
    if (!Object.keys(rates).length) throw fail(502, 'TCMB kur verisi okunamadı');
    const data = { tarih, rates };
    cache.set('tcmb:today', { at: Date.now(), data });
    return data;
  }
  const r4 = (n) => round(n, 4);
  const mid = (x) => (x.alis != null && x.satis != null ? (x.alis + x.satis) / 2 : (x.alis ?? x.satis));

  async function doviz(_, ctx) {
    const a = seg(ctx, 0).toUpperCase();
    const b = seg(ctx, 1).toUpperCase();
    const { tarih, rates } = await tcmbRates();
    const get = (code) => {
      if (code === 'TRY' || code === 'TL') return { isim: 'TÜRK LİRASI', alis: 1, satis: 1 };
      const x = rates[code];
      if (!x) throw fail(404, `Kur bulunamadı: ${code}. Liste için: /doviz`);
      return x;
    };
    if (!a) {
      return {
        tarih,
        kaynak: 'TCMB gösterge kurları (TL karşılığı)',
        kurlar: Object.entries(rates).map(([kod, x]) => ({ kod, isim: x.isim, alis: r4(x.alis), satis: r4(x.satis) })),
      };
    }
    if (!/^[A-Z]{2,3}$/.test(a) || (b && !/^[A-Z]{2,3}$/.test(b))) throw fail(400, 'Geçersiz para birimi kodu');
    if (!b) {
      const x = get(a);
      return { tarih, kod: a, isim: x.isim, birim: 1, alis_tl: r4(x.alis), satis_tl: r4(x.satis), efektif_alis_tl: r4(x.efektif_alis), efektif_satis_tl: r4(x.efektif_satis) };
    }
    const from = get(a), to = get(b);
    const amountRaw = ctx.q('miktar');
    const miktar = amountRaw ? num(amountRaw, 'miktar') : 1;
    if (!(miktar >= 0) || miktar > 1e12) throw fail(400, 'miktar geçersiz');
    const kur = mid(from) / mid(to);
    return {
      tarih,
      from: a === 'TL' ? 'TRY' : a,
      to: b === 'TL' ? 'TRY' : b,
      miktar,
      kur: sig(kur),
      sonuc: round(miktar * kur, 4),
      not: 'TCMB döviz alış-satış ortalamasıyla hesaplanır, bankalar farklı kur uygulayabilir.',
    };
  }

  function kdv(_, ctx) {
    const tutar = num(pathOrQuery(ctx, 0, 'tutar'), 'tutar');
    if (!(tutar >= 0) || tutar > 1e12) throw fail(400, 'tutar geçersiz');
    const oran = ctx.q('oran') ? num(ctx.q('oran'), 'oran') : 20;
    if (oran < 0 || oran > 100) throw fail(400, 'oran 0-100 arasında olmalı');
    const dahil = ['1', 'true', 'evet'].includes((ctx.q('dahil') || '').toLowerCase());
    const r2 = (n) => Math.round((n + Number.EPSILON) * 100) / 100;
    const matrah = dahil ? tutar / (1 + oran / 100) : tutar;
    const tax = dahil ? tutar - matrah : (tutar * oran) / 100;
    return { girilen_tutar: tutar, kdv_orani: oran, tutar_kdv_dahil: dahil, matrah: r2(matrah), kdv: r2(tax), toplam: r2(matrah + tax) };
  }

  // ----------------------------- DEPREM -------------------------------------
  async function deprem(_, ctx) {
    const min = clamp(ctx.q('min') ? num(ctx.q('min'), 'min') : 2, 0, 10);
    const limit = clamp(int(ctx.q('limit'), 10), 1, 50);
    const il = (ctx.q('il') || '').trim().slice(0, 50);
    return memo(`deprem:${min}:${limit}:${norm(il)}`, 60e3, async () => {
      const end = Date.now(), start = end - 3 * 864e5;
      const f = (ms) => new Date(ms).toISOString().slice(0, 19);
      let items = null, kaynak = 'AFAD';
      try {
        const r = await fetch(`https://deprem.afad.gov.tr/apiv2/event/filter?start=${f(start)}&end=${f(end)}&minmag=${min}&orderby=timedesc&limit=500`, { headers: UA, signal: AbortSignal.timeout(8000) });
        const j = r.ok ? await r.json() : null;
        if (Array.isArray(j)) {
          items = j.map((e) => {
            const ms = Date.parse(`${e.eventDate}Z`);
            return {
              tarih_tr: Number.isNaN(ms) ? null : trTime(ms),
              buyukluk: Number(e.magnitude),
              derinlik_km: round(Number(e.depth)),
              yer: e.location || null,
              il: e.province || null,
              ilce: e.district || null,
              enlem: Number(e.latitude),
              boylam: Number(e.longitude),
              tur: e.type || null,
            };
          });
        }
      } catch { /* USGS'e düş */ }
      if (!items) {
        kaynak = 'USGS (AFAD erişilemedi)';
        const j = await fetchJson(`https://earthquake.usgs.gov/fdsnws/event/1/query?format=geojson&minlatitude=35.5&maxlatitude=42.5&minlongitude=25.5&maxlongitude=45&starttime=${f(start)}&minmagnitude=${min}&orderby=time&limit=300`, { headers: UA }, 'Deprem servislerine ulaşılamadı');
        items = (j?.features || []).map((e) => ({
          tarih_tr: trTime(e.properties.time),
          buyukluk: e.properties.mag,
          derinlik_km: round(e.geometry?.coordinates?.[2]),
          yer: e.properties.place || null,
          il: null,
          ilce: null,
          enlem: e.geometry?.coordinates?.[1],
          boylam: e.geometry?.coordinates?.[0],
          tur: e.properties.type || null,
        }));
      }
      if (il) items = items.filter((e) => norm(`${e.il || ''} ${e.ilce || ''} ${e.yer || ''}`).includes(norm(il)));
      return { kaynak, pencere: 'son 72 saat', min_buyukluk: min, filtre_il: il || null, toplam_bulunan: items.length, depremler: items.slice(0, limit), saat_dilimi: 'Türkiye (UTC+3)' };
    });
  }

  // ----------------------------- VİKİPEDİ / BUGÜN ---------------------------
  async function wiki(_, ctx) {
    const konu = pathOrQuery(ctx, 0, 'q', 'konu');
    const rest = ctx.rest.length > 1 ? ctx.rest.map(dec).join('/') : konu;
    if (!rest) throw fail(400, 'Kullanım: /wiki/{konu}');
    if (rest.length > 200) throw fail(400, 'Konu en fazla 200 karakter olabilir');
    const dil = (ctx.q('dil') || 'tr').toLowerCase();
    if (!/^[a-z]{2,3}$/.test(dil)) throw fail(400, 'dil iki-üç harfli kod olmalı (örn. tr, en)');
    return memo(`wiki:${dil}:${rest.toLowerCase()}`, 60 * 60e3, async () => {
      let r;
      try {
        r = await fetch(`https://${dil}.wikipedia.org/api/rest_v1/page/summary/${encodeURIComponent(rest.replace(/ /g, '_'))}`, { headers: UA, signal: AbortSignal.timeout(10000) });
      } catch { throw fail(502, 'Vikipedi servisine ulaşılamadı'); }
      if (r.status === 404) throw fail(404, 'Madde bulunamadı');
      if (!r.ok) throw fail(502, `Vikipedi hata verdi (${r.status})`);
      const d = await r.json();
      return {
        baslik: d.title || rest,
        aciklama: d.description || null,
        ozet: d.extract || null,
        anlam_ayrimi: d.type === 'disambiguation',
        resim: d.thumbnail?.source || null,
        link: d.content_urls?.desktop?.page || null,
        dil,
      };
    });
  }

  async function bugun(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'tarih');
    let mo, d;
    if (raw) {
      const m = raw.match(/^(?:\d{4}-)?(\d{1,2})-(\d{1,2})$/);
      if (!m) throw fail(400, 'Tarih AA-GG biçiminde olmalı (örn. 10-29)');
      [mo, d] = [+m[1], +m[2]];
      const t = new Date(Date.UTC(2000, mo - 1, d));
      if (t.getUTCMonth() !== mo - 1 || t.getUTCDate() !== d) throw fail(400, 'Geçersiz tarih');
    } else { const t = trNow(); mo = t.m; d = t.d; }
    const tur = (ctx.q('tur') || 'events').toLowerCase();
    if (!['events', 'births', 'deaths', 'holidays'].includes(tur)) throw fail(400, 'tur: events, births, deaths veya holidays olmalı');
    const limit = clamp(int(ctx.q('limit'), 10), 1, 50);
    return memo(`bugun:${mo}-${d}:${tur}:${limit}`, 6 * 60 * 60e3, async () => {
      let dil = 'tr', j = null;
      for (const lang of ['tr', 'en']) {
        try {
          const r = await fetch(`https://api.wikimedia.org/feed/v1/wikipedia/${lang}/onthisday/${tur}/${pad(mo)}/${pad(d)}`, { headers: UA, signal: AbortSignal.timeout(10000) });
          if (r.ok) { j = await r.json(); dil = lang; break; }
        } catch { /* sonraki dil */ }
      }
      if (!j) throw fail(502, 'Tarihte bugün servisine ulaşılamadı');
      const list = (j[tur] || []).map((e) => ({ yil: e.year ?? null, metin: e.text || '' }));
      list.sort((a, b) => (b.yil ?? -1e9) - (a.yil ?? -1e9));
      return { tarih: `${d} ${MONTHS[mo - 1]}`, tur, dil, toplam: list.length, kayitlar: list.slice(0, limit) };
    });
  }

  // ----------------------------- PLAKA / BURÇ -------------------------------
  const IL = [
    [1, 'Adana', '322'], [2, 'Adıyaman', '416'], [3, 'Afyonkarahisar', '272'], [4, 'Ağrı', '472'], [5, 'Amasya', '358'], [6, 'Ankara', '312'],
    [7, 'Antalya', '242'], [8, 'Artvin', '466'], [9, 'Aydın', '256'], [10, 'Balıkesir', '266'], [11, 'Bilecik', '228'], [12, 'Bingöl', '426'],
    [13, 'Bitlis', '434'], [14, 'Bolu', '374'], [15, 'Burdur', '248'], [16, 'Bursa', '224'], [17, 'Çanakkale', '286'], [18, 'Çankırı', '376'],
    [19, 'Çorum', '364'], [20, 'Denizli', '258'], [21, 'Diyarbakır', '412'], [22, 'Edirne', '284'], [23, 'Elazığ', '424'], [24, 'Erzincan', '446'],
    [25, 'Erzurum', '442'], [26, 'Eskişehir', '222'], [27, 'Gaziantep', '342'], [28, 'Giresun', '454'], [29, 'Gümüşhane', '456'], [30, 'Hakkari', '438'],
    [31, 'Hatay', '326'], [32, 'Isparta', '246'], [33, 'Mersin', '324'], [34, 'İstanbul', '212 / 216'], [35, 'İzmir', '232'], [36, 'Kars', '474'],
    [37, 'Kastamonu', '366'], [38, 'Kayseri', '352'], [39, 'Kırklareli', '288'], [40, 'Kırşehir', '386'], [41, 'Kocaeli', '262'], [42, 'Konya', '332'],
    [43, 'Kütahya', '274'], [44, 'Malatya', '422'], [45, 'Manisa', '236'], [46, 'Kahramanmaraş', '344'], [47, 'Mardin', '482'], [48, 'Muğla', '252'],
    [49, 'Muş', '436'], [50, 'Nevşehir', '384'], [51, 'Niğde', '388'], [52, 'Ordu', '452'], [53, 'Rize', '464'], [54, 'Sakarya', '264'],
    [55, 'Samsun', '362'], [56, 'Siirt', '484'], [57, 'Sinop', '368'], [58, 'Sivas', '346'], [59, 'Tekirdağ', '282'], [60, 'Tokat', '356'],
    [61, 'Trabzon', '462'], [62, 'Tunceli', '428'], [63, 'Şanlıurfa', '414'], [64, 'Uşak', '276'], [65, 'Van', '432'], [66, 'Yozgat', '354'],
    [67, 'Zonguldak', '372'], [68, 'Aksaray', '382'], [69, 'Bayburt', '458'], [70, 'Karaman', '338'], [71, 'Kırıkkale', '318'], [72, 'Batman', '488'],
    [73, 'Şırnak', '486'], [74, 'Bartın', '378'], [75, 'Ardahan', '478'], [76, 'Iğdır', '476'], [77, 'Yalova', '226'], [78, 'Karabük', '370'],
    [79, 'Kilis', '348'], [80, 'Osmaniye', '328'], [81, 'Düzce', '380'],
  ];
  const ilOut = ([k, n, a]) => ({ plaka: pad(k), il: n, alan_kodu: a });

  function plaka(_, ctx) {
    const q = pathOrQuery(ctx, 0, 'q', 'kod', 'il');
    if (!q) return { toplam: IL.length, iller: IL.map(([k, n, a]) => `${pad(k)} ${n} (${a})`) };
    if (/^\d{1,2}$/.test(q)) {
      const hit = IL.find(([k]) => k === +q);
      if (!hit) throw fail(404, 'Plaka kodu 1-81 arasında olmalı');
      return ilOut(hit);
    }
    if (/^\d{3}$/.test(q)) {
      const hit = IL.filter(([, , a]) => a.split(' / ').includes(q));
      if (!hit.length) throw fail(404, 'Bu alan koduna ait il bulunamadı');
      return hit.length === 1 ? ilOut(hit[0]) : { sonuc: hit.map(ilOut) };
    }
    const n = norm(q);
    const hit = IL.find(([, name]) => norm(name) === n) || IL.find(([, name]) => norm(name).startsWith(n));
    if (!hit) throw fail(404, 'İl bulunamadı');
    return ilOut(hit);
  }

  const SIGNS = [
    ['Koç', 'Ateş', '21 Mart - 19 Nisan', 'Mars'], ['Boğa', 'Toprak', '20 Nisan - 20 Mayıs', 'Venüs'],
    ['İkizler', 'Hava', '21 Mayıs - 20 Haziran', 'Merkür'], ['Yengeç', 'Su', '21 Haziran - 22 Temmuz', 'Ay'],
    ['Aslan', 'Ateş', '23 Temmuz - 22 Ağustos', 'Güneş'], ['Başak', 'Toprak', '23 Ağustos - 22 Eylül', 'Merkür'],
    ['Terazi', 'Hava', '23 Eylül - 22 Ekim', 'Venüs'], ['Akrep', 'Su', '23 Ekim - 21 Kasım', 'Plüton'],
    ['Yay', 'Ateş', '22 Kasım - 21 Aralık', 'Jüpiter'], ['Oğlak', 'Toprak', '22 Aralık - 19 Ocak', 'Satürn'],
    ['Kova', 'Hava', '20 Ocak - 18 Şubat', 'Uranüs'], ['Balık', 'Su', '19 Şubat - 20 Mart', 'Neptün'],
  ];
  const BOUNDS = [[1, 1, 9], [1, 20, 10], [2, 19, 11], [3, 21, 0], [4, 20, 1], [5, 21, 2], [6, 21, 3], [7, 23, 4], [8, 23, 5], [9, 23, 6], [10, 23, 7], [11, 22, 8], [12, 22, 9]];
  const signOf = (m, d) => { let idx = 9; for (const [bm, bd, i] of BOUNDS) if (m > bm || (m === bm && d >= bd)) idx = i; return SIGNS[idx]; };
  const signOut = (s) => ({ burc: s[0], element: s[1], tarih_araligi: s[2], yonetici_gezegen: s[3] });

  function burc(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'tarih');
    if (!raw) return { burclar: SIGNS.map((s) => `${s[0]}: ${s[2]}`) };
    const md = raw.match(/^(\d{1,2})-(\d{1,2})$/);
    let m, d;
    if (md) {
      [m, d] = [+md[1], +md[2]];
      const t = new Date(Date.UTC(2000, m - 1, d));
      if (t.getUTCMonth() !== m - 1 || t.getUTCDate() !== d) throw fail(400, 'Geçersiz tarih');
    } else ({ m, d } = parseDate(raw));
    return { tarih: `${d} ${MONTHS[m - 1]}`, ...signOut(signOf(m, d)) };
  }

  // ----------------------------- HESAPLAMALAR -------------------------------
  const dim = (y, m1) => new Date(Date.UTC(y, m1, 0)).getUTCDate();
  function ymdDiff(a, b) {
    let y = b.y - a.y, m = b.m - a.m, d = b.d - a.d;
    if (d < 0) { m--; d += dim(b.y, b.m - 1); }
    if (m < 0) { y--; m += 12; }
    return { yil: y, ay: m, gun: d };
  }

  function yas(_, ctx) {
    const b = parseDate(pathOrQuery(ctx, 0, 'tarih', 'dogum') || (() => { throw fail(400, 'Kullanım: /yas/{yyyy-aa-gg}'); })(), 'Doğum tarihi');
    const t = trNow(), todayMs = Date.UTC(t.y, t.m - 1, t.d);
    if (b.ms > todayMs) throw fail(400, 'Doğum tarihi gelecekte olamaz');
    const diff = ymdDiff(b, t);
    const totalDays = Math.round((todayMs - b.ms) / 864e5);
    let next = Date.UTC(t.y, b.m - 1, b.d);
    if (next < todayMs) next = Date.UTC(t.y + 1, b.m - 1, b.d);
    return {
      dogum_tarihi: isoMs(b.ms),
      dogum_gunu: DAYS[new Date(b.ms).getUTCDay()],
      yas: diff.yil,
      ay: diff.ay,
      gun: diff.gun,
      toplam_gun: totalDays,
      toplam_hafta: Math.floor(totalDays / 7),
      toplam_ay: diff.yil * 12 + diff.ay,
      sonraki_dogum_gunu: isoMs(next),
      sonraki_dogum_gunune_kalan_gun: Math.round((next - todayMs) / 864e5),
      ...signOut(signOf(b.m, b.d)),
    };
  }

  function tarihFark(_, ctx) {
    const aRaw = pathOrQuery(ctx, 0, 'baslangic', 'a');
    if (!aRaw) throw fail(400, 'Kullanım: /tarihfark/{yyyy-aa-gg}/{yyyy-aa-gg}');
    const bRaw = pathOrQuery(ctx, 1, 'bitis', 'b');
    let a = parseDate(aRaw, 'Başlangıç tarihi');
    let b = bRaw ? parseDate(bRaw, 'Bitiş tarihi') : { ...trNow(), ms: trToday() };
    const reversed = a.ms > b.ms;
    if (reversed) [a, b] = [b, a];
    const days = Math.round((b.ms - a.ms) / 864e5);
    if (days > 36600) throw fail(400, 'Tarih aralığı en fazla 100 yıl olabilir');
    const holMaps = new Map();
    const holiday = (ms) => {
      const y = new Date(ms).getUTCFullYear();
      if (y < 2000 || y > 2100) return false;
      if (!holMaps.has(y)) holMaps.set(y, holidaysOf(y));
      const h = holMaps.get(y).get(isoMs(ms));
      return !!(h && !h.half);
    };
    let work = 0;
    for (let ms = a.ms; ms < b.ms; ms += 864e5) {
      const wd = new Date(ms).getUTCDay();
      if (wd !== 0 && wd !== 6 && !holiday(ms)) work++;
    }
    return {
      baslangic: isoMs(a.ms),
      bitis: isoMs(b.ms),
      yon: reversed ? 'geri (bitiş başlangıçtan önce, sıra düzeltildi)' : 'ileri',
      gun_farki: days,
      hafta: Math.floor(days / 7),
      hafta_artan_gun: days % 7,
      yil_ay_gun: ymdDiff(a, b),
      is_gunu: work,
      not: 'is_gunu hafta sonları ve resmi tatiller çıkarılarak hesaplanır; başlangıç günü dahil, bitiş günü hariçtir.',
    };
  }

  function bmi(_, ctx) {
    const boy = num(pathOrQuery(ctx, 0, 'boy'), 'boy (cm)');
    const kilo = num(pathOrQuery(ctx, 1, 'kilo'), 'kilo (kg)');
    if (boy < 50 || boy > 250) throw fail(400, 'boy 50-250 cm arasında olmalı');
    if (kilo < 10 || kilo > 400) throw fail(400, 'kilo 10-400 kg arasında olmalı');
    const h = boy / 100, v = kilo / (h * h);
    const kategori = v < 18.5 ? 'Zayıf' : v < 25 ? 'Normal' : v < 30 ? 'Fazla kilolu' : v < 35 ? 'Obez (1. derece)' : v < 40 ? 'Obez (2. derece)' : 'Obez (3. derece)';
    return {
      boy_cm: boy,
      kilo_kg: kilo,
      vki: round(v, 1),
      kategori,
      normal_vki_araligi: '18.5 - 24.9',
      normal_kilo_araligi_kg: `${round(18.5 * h * h, 1)} - ${round(24.9 * h * h, 1)}`,
      not: 'Vücut kitle indeksi genel bir göstergedir, tıbbi teşhis yerine geçmez.',
    };
  }

  const UNITS = {
    uzunluk: { mm: 0.001, cm: 0.01, m: 1, km: 1000, in: 0.0254, ft: 0.3048, yd: 0.9144, mi: 1609.344 },
    kutle: { mg: 1e-6, g: 0.001, kg: 1, ton: 1000, oz: 0.028349523125, lb: 0.45359237 },
    hacim: { ml: 0.001, l: 1, m3: 1000, gal: 3.785411784 },
    hiz: { ms: 1, kmh: 1 / 3.6, mph: 0.44704, kn: 0.514444444 },
    alan: { m2: 1, km2: 1e6, ha: 1e4, donum: 1000, acre: 4046.8564224, ft2: 0.09290304 },
    veri: { bit: 0.125, byte: 1, kb: 1e3, mb: 1e6, gb: 1e9, tb: 1e12, kib: 1024, mib: 1048576, gib: 1073741824 },
    sicaklik: { c: 1, f: 1, k: 1 },
  };
  const ALIAS = { km2: 'km2', 'm²': 'm2', 'km²': 'km2', 'ft²': 'ft2', 'm³': 'm3', 'km/h': 'kmh', 'm/s': 'ms', celsius: 'c', fahrenheit: 'f', kelvin: 'k', '°c': 'c', '°f': 'f', gallon: 'gal', knot: 'kn', 'dönüm': 'donum' };
  const unitKey = (u) => { const k = String(u).trim().toLowerCase(); return ALIAS[k] || k; };
  const catOf = (u) => Object.keys(UNITS).find((c) => Object.prototype.hasOwnProperty.call(UNITS[c], u));

  function birim(_, ctx) {
    if (!ctx.rest.length || !seg(ctx, 0)) return { kategoriler: Object.fromEntries(Object.entries(UNITS).map(([c, o]) => [c, Object.keys(o).join(', ')])), kullanim: '/birim/{deger}/{from}/{to} (örn. /birim/100/km/mi)' };
    const value = num(seg(ctx, 0), 'deger');
    const from = unitKey(seg(ctx, 1) || ctx.q('from') || ''), to = unitKey(seg(ctx, 2) || ctx.q('to') || '');
    if (!from || !to) throw fail(400, 'Kullanım: /birim/{deger}/{from}/{to}');
    const cf = catOf(from), ct = catOf(to);
    if (!cf) throw fail(400, `Bilinmeyen birim: ${from}. Liste için: /birim`);
    if (!ct) throw fail(400, `Bilinmeyen birim: ${to}. Liste için: /birim`);
    if (cf !== ct) throw fail(400, `Farklı türler çevrilemez (${cf} → ${ct})`);
    let result;
    if (cf === 'sicaklik') {
      const c = from === 'c' ? value : from === 'f' ? ((value - 32) * 5) / 9 : value - 273.15;
      result = to === 'c' ? c : to === 'f' ? (c * 9) / 5 + 32 : c + 273.15;
    } else result = (value * UNITS[cf][from]) / UNITS[cf][to];
    return { kategori: cf, deger: value, from, to, sonuc: sig(result) };
  }

  // ======================= 2. DALGA: günlük hayat ============================
  const r2 = (n) => Math.round((n + Number.EPSILON) * 100) / 100;
  const money = (raw, what, max = 1e12) => { const n = num(raw, what); if (!(n >= 0) || n > max) throw fail(400, `${what} geçersiz`); return n; };

  // ---- Finans hesaplayıcıları ----
  function kredi(_, ctx) {
    const P = money(pathOrQuery(ctx, 0, 'tutar'), 'tutar');
    const n = Math.trunc(num(pathOrQuery(ctx, 1, 'vade'), 'vade (ay)'));
    if (P <= 0) throw fail(400, 'tutar 0\'dan büyük olmalı');
    if (n < 1 || n > 480) throw fail(400, 'vade 1-480 ay arasında olmalı');
    if (!ctx.q('faiz')) throw fail(400, 'faiz gerekli (örn. ?faiz=3.5 aylık yüzde)');
    const rate = num(ctx.q('faiz'), 'faiz');
    if (rate < 0 || rate > 100) throw fail(400, 'faiz 0-100 arasında olmalı');
    const yillik = (ctx.q('tur') || 'aylik').toLowerCase() === 'yillik';
    const r = (yillik ? rate / 12 : rate) / 100;
    const pay = r === 0 ? P / n : (P * r) / (1 - Math.pow(1 + r, -n));
    let bal = P;
    const plan = [];
    for (let i = 1; i <= Math.min(n, 12); i++) {
      const interest = bal * r, principal = pay - interest;
      bal = Math.max(0, bal - principal);
      plan.push({ ay: i, taksit: r2(pay), anapara: r2(principal), faiz: r2(interest), kalan_borc: r2(bal) });
    }
    return {
      kredi_tutari: P, vade_ay: n, aylik_faiz_yuzde: round(r * 100, 4), yillik_basit_faiz_yuzde: round(r * 1200, 2),
      aylik_taksit: r2(pay), toplam_odeme: r2(pay * n), toplam_faiz: r2(pay * n - P),
      odeme_plani_ilk_12_ay: plan,
      not: 'KKDF, BSMV, masraf ve sigorta dahil değildir. Gerçek taksit bankanıza göre değişir.',
    };
  }

  function mevduat(_, ctx) {
    const P = money(pathOrQuery(ctx, 0, 'anapara'), 'anapara');
    const gun = Math.trunc(num(pathOrQuery(ctx, 1, 'gun'), 'gun'));
    if (gun < 1 || gun > 3650) throw fail(400, 'gun 1-3650 arasında olmalı');
    if (!ctx.q('faiz')) throw fail(400, 'faiz gerekli (örn. ?faiz=45 yıllık yüzde)');
    const faiz = num(ctx.q('faiz'), 'faiz');
    const stopaj = ctx.q('stopaj') ? num(ctx.q('stopaj'), 'stopaj') : 0;
    if (faiz < 0 || faiz > 1000 || stopaj < 0 || stopaj > 100) throw fail(400, 'faiz veya stopaj geçersiz');
    const brut = (P * faiz / 100 * gun) / 365;
    const tax = (brut * stopaj) / 100;
    return { anapara: P, gun, yillik_faiz_yuzde: faiz, stopaj_yuzde: stopaj, brut_getiri: r2(brut), stopaj_tutari: r2(tax), net_getiri: r2(brut - tax), vade_sonu_toplam: r2(P + brut - tax), not: 'Basit faiz, 365 gün üzerinden hesaplanır.' };
  }

  function indirim(_, ctx) {
    const fiyat = money(pathOrQuery(ctx, 0, 'fiyat'), 'fiyat');
    const oran = num(pathOrQuery(ctx, 1, 'oran'), 'oran');
    if (oran < 0 || oran > 100) throw fail(400, 'oran 0-100 arasında olmalı');
    const save = (fiyat * oran) / 100;
    return { eski_fiyat: fiyat, indirim_orani: oran, indirim_tutari: r2(save), yeni_fiyat: r2(fiyat - save) };
  }

  function yuzde(_, ctx) {
    const a = num(pathOrQuery(ctx, 0, 'a'), 'a'), b = num(pathOrQuery(ctx, 1, 'b'), 'b');
    return {
      a, b,
      [`${a}_in_yuzde_${b}_si`]: sig((a * b) / 100),
      [`${a}_artı_yuzde_${b}`]: sig(a + (a * b) / 100),
      [`${a}_eksi_yuzde_${b}`]: sig(a - (a * b) / 100),
      a_b_nin_yuzde_kaci: b === 0 ? null : sig((a / b) * 100),
      a_dan_b_ye_degisim_yuzde: a === 0 ? null : sig(((b - a) / a) * 100),
    };
  }

  function bahsis(_, ctx) {
    const hesap = money(pathOrQuery(ctx, 0, 'hesap'), 'hesap');
    const oran = ctx.q('yuzde') ? num(ctx.q('yuzde'), 'yuzde') : 10;
    const kisi = ctx.q('kisi') ? Math.trunc(num(ctx.q('kisi'), 'kisi')) : 1;
    if (oran < 0 || oran > 100 || kisi < 1 || kisi > 1000) throw fail(400, 'yuzde 0-100, kisi 1-1000 olmalı');
    const tip = (hesap * oran) / 100, total = hesap + tip;
    return { hesap, bahsis_yuzde: oran, bahsis: r2(tip), toplam: r2(total), kisi, kisi_basi: r2(total / kisi) };
  }

  // ---- Kripto (CoinGecko) ----
  const COINS = { btc: 'bitcoin', eth: 'ethereum', usdt: 'tether', bnb: 'binancecoin', sol: 'solana', xrp: 'ripple', usdc: 'usd-coin', ada: 'cardano', doge: 'dogecoin', trx: 'tron', avax: 'avalanche-2', ton: 'the-open-network', dot: 'polkadot', link: 'chainlink', ltc: 'litecoin', shib: 'shiba-inu' };
  async function kripto(_, ctx) {
    const c = seg(ctx, 0).toLowerCase();
    if (c && !/^[a-z0-9-]{2,50}$/.test(c)) throw fail(400, 'Geçersiz coin');
    const list = c ? [c] : ['btc', 'eth', 'bnb', 'sol', 'xrp', 'doge', 'ada', 'trx', 'avax', 'usdt'];
    const ids = list.map((x) => COINS[x] || x);
    return memo(`kripto:${ids.join(',')}`, 60e3, async () => {
      const j = await fetchJson(`https://api.coingecko.com/api/v3/simple/price?ids=${ids.join(',')}&vs_currencies=try,usd&include_24hr_change=true`, { headers: UA }, 'Kripto fiyat servisine ulaşılamadı');
      const rows = list.map((x, i) => {
        const d = j?.[ids[i]];
        return d ? { coin: x.toUpperCase(), id: ids[i], fiyat_try: sig(d.try), fiyat_usd: sig(d.usd), degisim_24s_yuzde: round(d.try_24h_change, 2) } : null;
      }).filter(Boolean);
      if (!rows.length) throw fail(404, 'Coin bulunamadı. CoinGecko kimliği veya btc, eth gibi kısa kod kullanın');
      return c ? { ...rows[0], kaynak: 'CoinGecko' } : { kaynak: 'CoinGecko', coinler: rows };
    });
  }

  // ---- Zaman & yer ----
  const offsetMin = (tz, date) => {
    const part = new Intl.DateTimeFormat('en-US', { timeZone: tz, timeZoneName: 'longOffset' }).formatToParts(date).find((x) => x.type === 'timeZoneName')?.value || 'GMT';
    const m = part.match(/GMT([+-])(\d{1,2}):?(\d{2})?/);
    return m ? (m[1] === '-' ? -1 : 1) * (+m[2] * 60 + +(m[3] || 0)) : 0;
  };
  const fmtOff = (min) => `${min < 0 ? '-' : '+'}${pad(Math.floor(Math.abs(min) / 60))}:${pad(Math.abs(min) % 60)}`;

  async function saat(_, ctx) {
    const arg = (ctx.rest.length ? ctx.rest.map(dec).join('/') : (ctx.q('q') || ctx.q('sehir') || '')).trim();
    if (!arg) throw fail(400, 'Kullanım: /saat/{şehir} veya /saat/Europe/London');
    if (arg.length > 100) throw fail(400, 'En fazla 100 karakter');
    let tz, konum = null;
    if (/^[A-Za-z_]+(\/[A-Za-z0-9_+\-]+)+$/.test(arg) || /^utc$/i.test(arg)) tz = arg;
    else { konum = await geocode(arg, countryArg(ctx)); tz = konum.saat_dilimi; }
    const now = new Date();
    let local, off, trOff, weekday;
    try {
      local = new Intl.DateTimeFormat('sv-SE', { timeZone: tz, year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false }).format(now);
      weekday = new Intl.DateTimeFormat('tr-TR', { timeZone: tz, weekday: 'long' }).format(now);
      off = offsetMin(tz, now); trOff = offsetMin('Europe/Istanbul', now);
    } catch { throw fail(400, 'Geçersiz zaman dilimi'); }
    const [tarih, zaman] = local.split(' ');
    const diff = (off - trOff) / 60;
    return { ...(konum ? { konum: `${konum.ad}, ${konum.ulke}` } : {}), zaman_dilimi: tz, tarih, saat: zaman, gun: weekday, utc_farki: fmtOff(off), turkiye_ile_fark_saat: diff, aciklama: diff === 0 ? 'Türkiye ile aynı saat' : `Türkiye'den ${Math.abs(diff)} saat ${diff > 0 ? 'ileride' : 'geride'}` };
  }

  async function mesafe(_, ctx) {
    const a = seg(ctx, 0) || (ctx.q('a') || '').trim(), b = seg(ctx, 1) || (ctx.q('b') || '').trim();
    if (!a || !b) throw fail(400, 'Kullanım: /mesafe/{şehir1}/{şehir2}');
    if (a.length > 100 || b.length > 100) throw fail(400, 'En fazla 100 karakter');
    return memo(`mesafe:${a.toLowerCase()}:${b.toLowerCase()}`, 6 * 60 * 60e3, async () => {
      const [g1, g2] = await Promise.all([geocode(a, ''), geocode(b, '')]);
      const rad = (x) => (x * Math.PI) / 180, R = 6371.0088;
      const dLat = rad(g2.enlem - g1.enlem), dLon = rad(g2.boylam - g1.boylam);
      const h = Math.sin(dLat / 2) ** 2 + Math.cos(rad(g1.enlem)) * Math.cos(rad(g2.enlem)) * Math.sin(dLon / 2) ** 2;
      const km = 2 * R * Math.asin(Math.sqrt(h));
      return { nereden: `${g1.ad}, ${g1.ulke}`, nereye: `${g2.ad}, ${g2.ulke}`, kus_ucusu_km: round(km, 1), kus_ucusu_mil: round(km / 1.609344, 1), not: 'Düz çizgi (kuş uçuşu) mesafedir; karayolu mesafesi genelde daha uzundur.' };
    });
  }

  function tatilKalan() {
    const t = trNow(), today = Date.UTC(t.y, t.m - 1, t.d);
    const upcoming = [];
    for (const y of [t.y, t.y + 1]) {
      for (const [date, e] of [...holidaysOf(y).entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
        const ms = Date.parse(`${date}T00:00:00Z`);
        if (ms >= today) upcoming.push({ tarih: date, gun: DAYS[new Date(ms).getUTCDay()], tatil: e.names.join(' / ') + (e.half ? ' (yarım gün)' : ''), kalan_gun: Math.round((ms - today) / 864e5) });
      }
    }
    const next = upcoming[0] || null;
    return { bugun: isoMs(today), sonraki_tatil: next, yaklasan_tatiller: upcoming.slice(0, 6), ...(RELIGIOUS[t.y] && RELIGIOUS[t.y + 1] ? {} : { not: REL_NOTE }) };
  }

  function hicri(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'tarih');
    const ms = raw ? parseDate(raw).ms + 12 * 36e5 : Date.now();
    try {
      const cal = 'tr-TR-u-ca-islamic-umalqura';
      const parts = new Intl.DateTimeFormat(cal, { day: 'numeric', month: 'long', year: 'numeric', timeZone: 'UTC' }).formatToParts(ms);
      const get = (t) => parts.find((p) => p.type === t)?.value;
      const monthNo = new Intl.DateTimeFormat(cal, { month: 'numeric', timeZone: 'UTC' }).formatToParts(ms).find((p) => p.type === 'month')?.value;
      const yil = parseInt(get('year') || get('relatedYear'), 10);
      return { miladi: isoMs(ms), hicri: `${get('day')} ${get('month')} ${yil}`, gun: +get('day'), ay_no: +monthNo, ay_adi: get('month'), yil, not: 'Umm el-Kura takvimine göre hesaplanır; Diyanet takvimiyle ±1 gün fark olabilir.' };
    } catch { throw fail(501, 'Bu sunucuda hicri takvim desteklenmiyor'); }
  }

  // ---- Sözlük & çeviri & yazı ----
  async function sozluk(_, ctx) {
    const w = pathOrQuery(ctx, 0, 'q', 'kelime');
    if (!w) throw fail(400, 'Kullanım: /sozluk/{kelime}');
    if (w.length > 60) throw fail(400, 'Kelime en fazla 60 karakter olabilir');
    return memo(`sozluk:${w.toLocaleLowerCase('tr')}`, 24 * 60 * 60e3, async () => {
      let r;
      try { r = await fetch(`https://sozluk.gov.tr/gts?ara=${encodeURIComponent(w)}`, { headers: UA, signal: AbortSignal.timeout(10000) }); } catch { throw fail(502, 'TDK sözlük servisine ulaşılamadı'); }
      if (!r.ok) throw fail(502, 'TDK sözlük servisi hata verdi');
      const j = await r.json().catch(() => null);
      if (!Array.isArray(j) || !j.length) throw fail(404, 'Kelime bulunamadı');
      return {
        kelime: j[0].madde || w,
        anlamlar: (j[0].anlamlarListe || []).slice(0, 8).map((a) => ({ tur: (a.ozelliklerListe || []).map((o) => o.tam_adi).filter(Boolean).join(', ') || null, anlam: a.anlam, ornek: a.orneklerListe?.[0]?.ornek || null })),
        kaynak: 'TDK Güncel Türkçe Sözlük',
      };
    });
  }

  async function cevir(_, ctx) {
    const q = (ctx.rest.length ? ctx.rest.map(dec).join('/') : ctx.q('q') || '').trim();
    if (!q) throw fail(400, 'Kullanım: /cevir?q=hello&to=tr (veya /cevir/{metin}?to=en)');
    if (q.length > 500) throw fail(400, 'Metin en fazla 500 karakter olabilir');
    const to = (ctx.q('to') || 'tr').toLowerCase(), from = (ctx.q('from') || '').toLowerCase();
    if (!/^[a-z]{2,3}(-[a-z]{2})?$/.test(to) || (from && !/^[a-z]{2,3}(-[a-z]{2})?$/.test(from))) throw fail(400, 'Dil kodu geçersiz (örn. tr, en, de)');
    return memo(`cevir:${from}:${to}:${q.toLowerCase()}`, 6 * 60 * 60e3, async () => {
      const j = await fetchJson(`https://api.mymemory.translated.net/get?q=${encodeURIComponent(q)}&langpair=${from || 'Autodetect'}|${to}`, { headers: UA }, 'Çeviri servisine ulaşılamadı');
      const out = j?.responseData?.translatedText;
      if (!out || Number(j.responseStatus) !== 200) throw fail(502, j?.responseDetails || 'Çeviri yapılamadı');
      return { metin: q, ceviri: out, from: from || 'otomatik', to, kaynak: 'MyMemory' };
    });
  }

  function romen(_, ctx) {
    const raw = seg(ctx, 0) || (ctx.q('q') || '').trim();
    if (!raw) throw fail(400, 'Kullanım: /romen/{sayı veya romen rakamı}');
    const T = [[1000, 'M'], [900, 'CM'], [500, 'D'], [400, 'CD'], [100, 'C'], [90, 'XC'], [50, 'L'], [40, 'XL'], [10, 'X'], [9, 'IX'], [5, 'V'], [4, 'IV'], [1, 'I']];
    if (/^\d+$/.test(raw)) {
      let n = +raw;
      if (n < 1 || n > 3999) throw fail(400, 'Sayı 1-3999 arasında olmalı');
      const orig = n; let out = '';
      for (const [v, s] of T) while (n >= v) { out += s; n -= v; }
      return { sayi: orig, romen: out };
    }
    const s = raw.toUpperCase();
    if (!/^[MDCLXVI]+$/.test(s)) throw fail(400, 'Geçersiz romen rakamı');
    const val = { I: 1, V: 5, X: 10, L: 50, C: 100, D: 500, M: 1000 };
    let n = 0;
    for (let i = 0; i < s.length; i++) n += val[s[i]] < (val[s[i + 1]] || 0) ? -val[s[i]] : val[s[i]];
    let back = '', t = n;
    for (const [v, sym] of T) while (t >= v) { back += sym; t -= v; }
    if (back !== s) throw fail(400, 'Geçersiz romen rakamı');
    return { romen: s, sayi: n };
  }

  const ONES = ['', 'bir', 'iki', 'üç', 'dört', 'beş', 'altı', 'yedi', 'sekiz', 'dokuz'];
  const TENS = ['', 'on', 'yirmi', 'otuz', 'kırk', 'elli', 'altmış', 'yetmiş', 'seksen', 'doksan'];
  const SCALES = ['', 'bin', 'milyon', 'milyar', 'trilyon', 'katrilyon'];
  const words3 = (n) => [n >= 200 ? ONES[Math.floor(n / 100)] : '', n >= 100 ? 'yüz' : '', TENS[Math.floor((n % 100) / 10)], ONES[n % 10]].filter(Boolean).join(' ');
  function numWords(n) {
    if (n === 0) return 'sıfır';
    const groups = [];
    while (n > 0) { groups.push(n % 1000); n = Math.floor(n / 1000); }
    const out = [];
    for (let i = groups.length - 1; i >= 0; i--) {
      const g = groups[i];
      if (!g) continue;
      out.push(g === 1 && i === 1 ? 'bin' : [words3(g), SCALES[i]].filter(Boolean).join(' '));
    }
    return out.join(' ');
  }
  function yaziyla(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'tutar', 'sayi');
    const n = money(raw, 'tutar', 999999999999999);
    const kurusTotal = Math.round(n * 100);
    const lira = Math.floor(kurusTotal / 100), kurus = kurusTotal % 100;
    const liraW = numWords(lira), kurusW = numWords(kurus);
    return {
      tutar: kurusTotal / 100,
      lira_yazisi: `${liraW} lira${kurus ? ` ${kurusW} kuruş` : ''}`,
      sayi_yazisi: kurus ? `${liraW} virgül ${kurusW}` : liraW,
      cek_yazisi: `#${liraW} Türk Lirası${kurus ? ` ${kurusW} Kuruş` : ''}#`,
    };
  }

  // ---- Eğlence & karar ----
  const { randomInt } = require('crypto');
  function loto(_, ctx) {
    const kind = norm(seg(ctx, 0) || ctx.q('tur') || '');
    const GAMES = { sayisal: [[6, 90]], sanstopu: [[5, 34], [1, 14]], onnumara: [[10, 80]], superloto: [[6, 60]] };
    if (!kind) return { oyunlar: ['sayisal (6/90)', 'sanstopu (5/34 + 1/14)', 'onnumara (10/80)', 'superloto (6/60)'], kullanim: '/loto/sayisal?kolon=3' };
    const g = GAMES[kind.replace(/[^a-z]/g, '')];
    if (!g) throw fail(404, 'Oyun bulunamadı: sayisal, sanstopu, onnumara, superloto');
    const cols = clamp(int(ctx.q('kolon'), 1), 1, 10);
    const pick = (k, max) => { const s = new Set(); while (s.size < k) s.add(randomInt(1, max + 1)); return [...s].sort((a, b) => a - b); };
    return { oyun: kind, kolonlar: Array.from({ length: cols }, () => g.map(([k, max]) => pick(k, max).join(' ')).join(' + ')), not: 'Eğlence amaçlı rastgele sayılardır, kazanma ihtimalini artırmaz.' };
  }

  function rastgele(_, ctx) {
    const min = Math.trunc(num(pathOrQuery(ctx, 0, 'min') || '1', 'min')), max = Math.trunc(num(pathOrQuery(ctx, 1, 'max') || '100', 'max'));
    if (min > max || max - min > 1e9 || Math.abs(min) > 1e12 || Math.abs(max) > 1e12) throw fail(400, 'Aralık geçersiz (min <= max, en fazla 1 milyar genişlik)');
    const adet = clamp(int(ctx.q('adet'), 1), 1, 100);
    const uniq = ['1', 'true', 'evet'].includes((ctx.q('tekrarsiz') || '').toLowerCase());
    if (uniq && adet > max - min + 1) throw fail(400, 'Tekrarsız sayı adedi aralıktan büyük olamaz');
    const out = [];
    if (uniq) { const s = new Set(); while (s.size < adet) s.add(randomInt(min, max + 1)); out.push(...s); } else for (let i = 0; i < adet; i++) out.push(randomInt(min, max + 1));
    return { min, max, adet, sayilar: adet === 1 ? undefined : out, sayi: adet === 1 ? out[0] : undefined };
  }

  function sec(_, ctx) {
    const raw = ctx.rest.length ? ctx.rest.map(dec).join('/') : ctx.q('liste') || '';
    const items = raw.split(/[,;\n]/).map((x) => x.trim()).filter(Boolean);
    if (items.length < 2) throw fail(400, 'En az iki seçenek gerekli. Örn: /sec?liste=pizza,kebap,lahmacun');
    if (items.length > 50 || raw.length > 1000) throw fail(400, 'En fazla 50 seçenek / 1000 karakter');
    return { secenekler: items.length, secilen: items[randomInt(0, items.length)] };
  }

  const ATASOZLERI = [
    ['Damlaya damlaya göl olur.', 'Küçük birikimler zamanla büyük sonuç verir.'],
    ['Sakla samanı, gelir zamanı.', 'Bugün gereksiz görünen şey ileride işe yarayabilir.'],
    ['Ak akçe kara gün içindir.', 'Birikim, zor günlerde kullanılmak üzere saklanmalıdır.'],
    ['Acele işe şeytan karışır.', 'Aceleyle yapılan işte hata çıkar.'],
    ['Gülü seven dikenine katlanır.', 'Sevilen şey için zorluklara katlanmak gerekir.'],
    ['Bir elin nesi var, iki elin sesi var.', 'Birlik ve işbirliği güç verir.'],
    ['Komşu komşunun külüne muhtaçtır.', 'İnsanlar birbirlerine ihtiyaç duyar.'],
    ['Ağaç yaşken eğilir.', 'Eğitim ve terbiye küçük yaşta daha kolay verilir.'],
    ['Sabreden derviş muradına ermiş.', 'Sabırla beklemek insanı isteğine kavuşturur.'],
    ['Dost acı söyler.', 'Gerçek dost doğruyu hoşa gitmese de söyler.'],
    ['Bugünün işini yarına bırakma.', 'İşler ertelenmeden zamanında yapılmalıdır.'],
    ['Üzüm üzüme baka baka kararır.', 'İnsan çevresindekilerden etkilenir.'],
    ['Bir musibet bin nasihatten yeğdir.', 'Başa gelen bir sıkıntı, öğütten çok ders verir.'],
    ['Ne ekersen onu biçersin.', 'Yaptığının karşılığını görürsün.'],
    ['Taş yerinde ağırdır.', 'Her şey kendi yerinde değerlidir.'],
    ['Düşenin dostu olmaz.', 'Zor duruma düşen kişiyi çoğu kimse yalnız bırakır.'],
    ['Sabır acıdır, meyvesi tatlıdır.', 'Sabırla beklemek sonunda iyi sonuç verir.'],
    ['Çok gezen çok bilir.', 'Çok yer gören kişi tecrübe kazanır.'],
    ['Zararın neresinden dönülürse kârdır.', 'Yanlışı fark edince vazgeçmek kazançtır.'],
    ['Bin düşün, bir söyle.', 'Konuşmadan önce iyice düşünmek gerekir.'],
    ['Her yiğidin bir yoğurt yiyişi vardır.', 'Herkesin iş yapış biçimi farklıdır.'],
    ['Mum dibine ışık vermez.', 'Kişi çoğu zaman en yakınındakilere faydalı olamaz.'],
    ['Kervan yolda düzülür.', 'İş yapılırken eksikler tamamlanır, her şey baştan hazır olmaz.'],
  ];
  function atasozu(_, ctx) {
    let i;
    if (ctx.q('no')) { i = int(ctx.q('no'), 0) - 1; if (i < 0 || i >= ATASOZLERI.length) throw fail(400, `no 1-${ATASOZLERI.length} arasında olmalı`); }
    else if (['1', 'true', 'evet'].includes((ctx.q('gunluk') || '').toLowerCase())) i = Math.floor(trToday() / 864e5) % ATASOZLERI.length;
    else i = randomInt(0, ATASOZLERI.length);
    return { no: i + 1, toplam: ATASOZLERI.length, atasozu: ATASOZLERI[i][0], anlami: ATASOZLERI[i][1] };
  }

  // ======================= 3. DALGA: gündelik + bot eğlence ===================
  const pick = (arr) => arr[randomInt(0, arr.length)];
  const shuffle = (arr) => { const a = [...arr]; for (let i = a.length - 1; i > 0; i--) { const j = randomInt(0, i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; };
  const trLower = (s) => String(s).toLocaleLowerCase('tr');
  const trUpper = (s) => String(s).toLocaleUpperCase('tr');
  const clip = (s, n, what) => { const v = String(s ?? '').trim(); if (v.length > n) throw fail(400, `${what} en fazla ${n} karakter olabilir`); return v; };
  const hashInt = (str) => parseInt(require('crypto').createHash('sha256').update(str).digest('hex').slice(0, 8), 16);
  const hhmm = (min) => `${pad(Math.floor(min / 60) % 24)}:${pad(((min % 60) + 60) % 60)}`;
  const wantsTrue = (v) => ['1', 'true', 'evet'].includes(String(v || '').toLowerCase());
  const cleanName = (s, what) => clip(String(s || '').replace(/[\u0000-\u001f]/g, ''), 40, what);

  // ---- 1. /gno ----
  const GRADE = { AA: 4, BA: 3.5, BB: 3, CB: 2.5, CC: 2, DC: 1.5, DD: 1, FD: 0.5, FF: 0 };
  const scoreToGrade = (p) => (p >= 90 ? 'AA' : p >= 85 ? 'BA' : p >= 80 ? 'BB' : p >= 75 ? 'CB' : p >= 70 ? 'CC' : p >= 65 ? 'DC' : p >= 60 ? 'DD' : p >= 50 ? 'FD' : 'FF');
  function gno(_, ctx) {
    const raw = (ctx.rest.length ? ctx.rest.map(dec).join('/') : ctx.q('dersler') || '').trim();
    if (!raw) throw fail(400, 'Kullanım: /gno?dersler=AA:3,BB:4,CC:2 (not:kredi) veya 85:3 (puan:kredi)');
    const items = raw.split(/[,;]/).map((x) => x.trim()).filter(Boolean);
    if (items.length > 60) throw fail(400, 'En fazla 60 ders girilebilir');
    let pts = 0, cr = 0;
    const rows = [];
    for (const it of items) {
      const [g, k] = it.split(':').map((x) => x.trim());
      const kredi = num(k ?? '1', 'kredi');
      if (!(kredi > 0) || kredi > 30) throw fail(400, 'kredi 0-30 arasında olmalı');
      let harf = trUpper(g || '');
      if (/^\d+([.,]\d+)?$/.test(g || '')) harf = scoreToGrade(num(g, 'puan'));
      if (!(harf in GRADE)) throw fail(400, `Geçersiz not: ${g}`);
      pts += GRADE[harf] * kredi; cr += kredi;
      rows.push(`${harf} x ${kredi} kredi`);
    }
    const avg = pts / cr;
    return {
      ders_sayisi: rows.length, toplam_kredi: cr, gno: round(avg, 2), skala: '4.00',
      onur: avg >= 3.5 ? 'Yüksek onur' : avg >= 3 ? 'Onur' : 'Yok',
      dersler: rows,
      not: 'Harf katsayıları AA=4.0 ... FF=0 kabul edilir. Puan girerseniz yaygın 100\'lük tablo (90=AA, 85=BA, ...) kullanılır; üniversiteniz farklı olabilir.',
    };
  }

  // ---- 2. /gecmenotu ----
  function gecmenotu(_, ctx) {
    const vize = num(pathOrQuery(ctx, 0, 'vize'), 'vize');
    const oran = ctx.q('vizeoran') ? num(ctx.q('vizeoran'), 'vizeoran') : 40;
    const gecme = ctx.q('gecme') ? num(ctx.q('gecme'), 'gecme') : 60;
    if (vize < 0 || vize > 100 || gecme < 0 || gecme > 100) throw fail(400, 'Notlar 0-100 arasında olmalı');
    if (oran < 1 || oran > 99) throw fail(400, 'vizeoran 1-99 arasında olmalı');
    const need = (gecme - (vize * oran) / 100) / ((100 - oran) / 100);
    return {
      vize, vize_orani_yuzde: oran, final_orani_yuzde: 100 - oran, gecme_notu: gecme,
      gereken_final: round(Math.max(0, need), 2),
      durum: need <= 0 ? 'Finalden 0 alsanız bile ortalama olarak geçersiniz' : need > 100 ? 'Final 100 olsa bile ortalama geçme notuna ulaşılamaz' : 'Finalden en az bu notu almalısınız',
      not: 'Bazı okullar finalden ayrıca alt sınır (örn. 50) arar, yönergenize bakın.',
    };
  }

  // ---- 3. /boya ----
  function boya(_, ctx) {
    const en = money(seg(ctx, 0) || ctx.q('en'), 'en (m)', 100), boy = money(seg(ctx, 1) || ctx.q('boy'), 'boy (m)', 100), h = money(seg(ctx, 2) || ctx.q('yukseklik') || '2.6', 'yukseklik (m)', 10);
    if (!en || !boy || !h) throw fail(400, 'Kullanım: /boya/{en}/{boy}/{yukseklik} (metre)');
    const kapi = clamp(int(ctx.q('kapi'), 1), 0, 20), pencere = clamp(int(ctx.q('pencere'), 1), 0, 30), kat = clamp(int(ctx.q('kat'), 2), 1, 5);
    const verim = ctx.q('verim') ? num(ctx.q('verim'), 'verim') : 10;
    if (!(verim >= 3 && verim <= 20)) throw fail(400, 'verim (m2/litre) 3-20 arasında olmalı');
    const duvar = 2 * (en + boy) * h - kapi * 1.9 - pencere * 1.5;
    if (duvar <= 0) throw fail(400, 'Kapı ve pencere alanı duvar alanından büyük görünüyor');
    const zemin = en * boy;
    const litreDuvar = (duvar * kat) / verim, litreTavan = (zemin * kat) / verim;
    return {
      oda: `${en} x ${boy} x ${h} m`, kapi_adedi: kapi, pencere_adedi: pencere, kat_sayisi: kat,
      duvar_alani_m2: round(duvar, 1), tavan_zemin_alani_m2: round(zemin, 1),
      duvar_boyasi_litre: round(litreDuvar, 1), tavan_boyasi_litre: round(litreTavan, 1),
      toplam_boya_litre: round(litreDuvar + litreTavan, 1), onerilen_15_litre_kova: Math.ceil((litreDuvar + litreTavan) / 15),
      parke_paketi_adet: Math.ceil((zemin * 1.1) / 2.2), fayans_30x60_adet: Math.ceil((zemin * 1.1) / 0.18),
      not: 'Boyada 1 litre yaklaşık 10 m2 (tek kat) kabul edilir, parke 2.2 m2/paket, fayans 30x60 cm ve %10 fire eklenmiştir.',
    };
  }

  // ---- 4. /elektrik ----
  function elektrik(_, ctx) {
    const watt = money(pathOrQuery(ctx, 0, 'watt'), 'watt', 1e6), saat = money(pathOrQuery(ctx, 1, 'saat'), 'saat (günlük)', 24);
    if (!ctx.q('fiyat')) throw fail(400, 'fiyat gerekli: kWh başına TL (örn. ?fiyat=3.2). Faturanızdaki birim fiyatı yazın.');
    const fiyat = num(ctx.q('fiyat'), 'fiyat'), gun = clamp(int(ctx.q('gun'), 30), 1, 366);
    const kwh = (watt * saat * gun) / 1000;
    return { cihaz_gucu_watt: watt, gunluk_kullanim_saat: saat, gun, toplam_kwh: round(kwh, 2), birim_fiyat_tl: fiyat, maliyet_tl: r2(kwh * fiyat), yillik_tahmin_tl: r2(((watt * saat * 365) / 1000) * fiyat) };
  }

  // ---- 5. /klima ----
  const BTU = [7000, 9000, 12000, 18000, 24000, 30000, 36000];
  function klima(_, ctx) {
    const m2 = money(pathOrQuery(ctx, 0, 'm2'), 'm2', 1000);
    if (!m2) throw fail(400, 'm2 0\'dan büyük olmalı');
    const ustKat = wantsTrue(ctx.q('ustkat')), gunes = wantsTrue(ctx.q('gunes')), kisi = clamp(int(ctx.q('kisi'), 2), 1, 50);
    let btu = m2 * 350;
    if (ustKat) btu *= 1.1;
    if (gunes) btu *= 1.1;
    btu += Math.max(0, kisi - 2) * 600;
    return { oda_m2: m2, hesaplanan_btu: Math.round(btu), onerilen_btu: BTU.find((b) => b >= btu) || `${Math.ceil(btu / 6000) * 6000} (birden fazla cihaz düşünün)`, kisi, ust_kat: ustKat, cok_gunes_alan: gunes, not: 'Kaba bir tahmindir. Tavan yüksekliği ve yalıtım sonucu değiştirir.' };
  }

  // ---- 6. /tuketim ----
  function tuketim(_, ctx) {
    const v = num(seg(ctx, 0), 'deger'), from = trLower(seg(ctx, 1)), to = trLower(seg(ctx, 2));
    const U = ['l100', 'kml', 'mpg', 'mpguk'];
    if (!U.includes(from) || !U.includes(to)) throw fail(400, 'Kullanım: /tuketim/{deger}/{from}/{to}. Birimler: l100 (litre/100km), kml (km/litre), mpg (ABD), mpguk (İngiliz)');
    if (!(v > 0)) throw fail(400, 'deger 0\'dan büyük olmalı');
    const l100 = from === 'l100' ? v : from === 'kml' ? 100 / v : from === 'mpg' ? 235.214583 / v : 282.480936 / v;
    const out = to === 'l100' ? l100 : to === 'kml' ? 100 / l100 : to === 'mpg' ? 235.214583 / l100 : 282.480936 / l100;
    return { deger: v, from, to, sonuc: sig(out) };
  }

  // ---- 7. /tarihyazi ----
  function tarihyazi(_, ctx) {
    const d = parseDate(pathOrQuery(ctx, 0, 'tarih'));
    return { tarih: `${pad(d.d)}.${pad(d.m)}.${d.y}`, yazi: `${numWords(d.d)} ${trLower(MONTHS[d.m - 1])} ${numWords(d.y)}`, gun: DAYS[new Date(d.ms).getUTCDay()] };
  }

  // ---- 8. /telefon ----
  function telefon(_, ctx) {
    const raw = pathOrQuery(ctx, 0, 'no', 'q');
    if (!raw) throw fail(400, 'Kullanım: /telefon/{numara}');
    let d = raw.replace(/[^\d+]/g, '').replace(/^\+/, '');
    if (d.startsWith('0090')) d = d.slice(4); else if (d.startsWith('90') && d.length >= 12) d = d.slice(2); else if (d.startsWith('0')) d = d.slice(1);
    const out = (ok, extra) => ({ girilen: raw.slice(0, 30), gecerli: ok, ...extra });
    if (/^(444\d{4}|(800|850)\d{7})$/.test(d)) return out(true, { tur: 'Özel hizmet numarası', numara: d });
    if (!/^\d{10}$/.test(d)) return out(false, { neden: 'Numara 10 haneli olmalı (başındaki 0 veya +90 hariç)' });
    const f = `${d.slice(3, 6)} ${d.slice(6, 8)} ${d.slice(8)}`;
    const base = { tur: null, ulusal: `0 (${d.slice(0, 3)}) ${f}`, uluslararasi: `+90 ${d.slice(0, 3)} ${f}`, e164: `+90${d}` };
    if (d[0] === '5') return out(true, { ...base, tur: 'Cep telefonu' });
    if (/^[234]/.test(d)) {
      const il = IL.filter(([, , a]) => a.split(' / ').includes(d.slice(0, 3)));
      if (!il.length) return out(false, { neden: `Bilinmeyen alan kodu: ${d.slice(0, 3)}` });
      return out(true, { ...base, tur: 'Sabit hat', alan_kodu_il: il.map(([, n]) => n).join(' / ') });
    }
    return out(false, { neden: 'Türkiye numarası 2, 3, 4 veya 5 ile başlamalı' });
  }

  // ---- 9. /dilekce ----
  function dilekce(_, ctx) {
    const konu = clip(ctx.q('konu') || pathOrQuery(ctx, 0), 150, 'konu');
    if (!konu) throw fail(400, 'Kullanım: /dilekce?konu=...&kurum=...&ad=...&aciklama=...');
    const kurum = clip(ctx.q('kurum') || 'İlgili Makama', 100, 'kurum'), ad = clip(ctx.q('ad'), 80, 'ad'), tc = clip(ctx.q('tc'), 11, 'tc'), adres = clip(ctx.q('adres'), 200, 'adres');
    const aciklama = clip(ctx.q('aciklama'), 800, 'aciklama') || `${konu} hususunda gereğinin yapılmasını arz ederim.`;
    const t = trNow();
    const lines = [trUpper(kurum), 'SAYIN YETKİLİSİNE', '', `KONU: ${konu}`, '', aciklama, 'Gereğini bilgilerinize saygılarımla arz ederim.', '', `Tarih: ${pad(t.d)}.${pad(t.m)}.${t.y}`];
    lines.push(`Ad Soyad: ${ad || '................'}`);
    lines.push(`T.C. Kimlik No: ${tc || '................'}`);
    lines.push(`Adres: ${adres || '................'}`);
    lines.push('İmza:');
    return { satirlar: lines, not: 'Taslaktır, kurumunuzun gereksinimine göre düzenleyin.' };
  }

  // ---- 10. /mesaj ----
  const MESAJLAR = {
    bayram: ['Bayramın sevdiklerinle huzur ve sağlık içinde geçsin.', 'Bu bayramın sofrası bereketli, kalbin neşeli olsun.', 'Bayramın mübarek olsun, nice bayramlara birlikte ulaşalım.', 'Sevdiklerinle dolu, güzel bir bayram dilerim.'],
    dogumgunu: ['Yeni yaşın sağlık, mutluluk ve başarı getirsin. İyi ki doğdun.', 'Doğum günün kutlu olsun, dilediğin her şey gerçekleşsin.', 'Yeni yaşında yüzünden gülümseme eksik olmasın.', 'Nice sağlıklı ve mutlu yıllara. Doğum günün kutlu olsun.'],
    gecmisolsun: ['Geçmiş olsun, bir an önce iyileşmeni diliyorum.', 'Acil şifalar dilerim, kendine iyi bak.', 'Sağlığına kavuşmanı sabırsızlıkla bekliyoruz, geçmiş olsun.', 'Geçmiş olsun, dinlen ve toparlan, her şey yoluna girecek.'],
    yeniyil: ['Yeni yılın sağlık ve başarı getirsin.', 'Yeni yıl, kalbinden geçen her güzelliği getirsin.', 'Yeni yılda hayallerinin peşinden gideceğin güçlü bir yıl dilerim.', 'Mutlu yıllar, bol şanslı ve huzurlu bir yıl olsun.'],
    tebrik: ['Başarını gönülden kutluyorum, daha nicelerine.', 'Emeğinin karşılığını aldın, seninle gurur duyuyoruz.', 'Tebrikler, bu başarı çok yakışıyor.', 'Yeni yolunda başarılar, kutlu olsun.'],
    hayirliolsun: ['Yeni evin hayırlı olsun, huzurla yaşayın.', 'Yeni işin hayırlı olsun, başarılarının devamını dilerim.', 'Hayırlı olsun, bereketli ve uğurlu günler dilerim.', 'Yeni adımın hayırlı olsun.'],
    gunaydin: ['Günaydın, güzel bir gün olsun.', 'Günaydın, kahven sıcak, gününün tadı tatlı olsun.', 'Güne gülümseyerek başla, günaydın.', 'Günaydın, bugün her şey yolunda gitsin.'],
    iyigeceler: ['İyi geceler, tatlı rüyalar.', 'Rahat bir uyku dilerim, iyi geceler.', 'Yarın daha güzel bir güne uyanman dileğiyle, iyi geceler.', 'Huzurlu bir gece olsun, iyi geceler.'],
  };
  function mesaj(_, ctx) {
    const tur = norm(pathOrQuery(ctx, 0, 'tur')).replace(/[^a-z]/g, '');
    if (!tur) return { turler: Object.keys(MESAJLAR), kullanim: '/mesaj/bayram?isim=Ayşe' };
    const list = MESAJLAR[tur];
    if (!list) throw fail(404, `Tür bulunamadı. Türler: ${Object.keys(MESAJLAR).join(', ')}`);
    const isim = cleanName(ctx.q('isim'), 'isim'), m = pick(list);
    return { tur, mesaj: isim ? `${isim}, ${trLower(Array.from(m)[0])}${Array.from(m).slice(1).join('')}` : m };
  }

  // ---- 11. /hesapla (güvenli ifade çözücü) ----
  function evalExpr(src) {
    const s = src.replace(/×/g, '*').replace(/÷/g, '/').replace(/(?<=\d)x(?=\d)/gi, '*').replace(/\s+/g, '');
    const toks = s.match(/\d+(?:\.\d+)?|[a-zA-Z]+|[-+*/^%(),]/g) || [];
    if (toks.join('') !== s) throw fail(400, 'İfadede geçersiz karakter var');
    if (toks.length > 200) throw fail(400, 'İfade çok uzun');
    let i = 0;
    const FN = { sqrt: Math.sqrt, abs: Math.abs, sin: Math.sin, cos: Math.cos, tan: Math.tan, log: Math.log10, ln: Math.log, exp: Math.exp, round: Math.round, floor: Math.floor, ceil: Math.ceil, min: Math.min, max: Math.max, pow: Math.pow };
    const CONST = { pi: Math.PI, e: Math.E };
    const peek = () => toks[i];
    const eat = (t) => { if (toks[i] !== t) throw fail(400, `İfade hatalı: "${t}" bekleniyordu`); i++; };
    const expr = () => { let v = term(); while (peek() === '+' || peek() === '-') v = toks[i++] === '+' ? v + term() : v - term(); return v; };
    const term = () => { let v = unary(); while (['*', '/', '%'].includes(peek())) { const o = toks[i++], r = unary(); v = o === '*' ? v * r : o === '/' ? v / r : v % r; } return v; };
    const unary = () => { if (peek() === '-') { i++; return -unary(); } if (peek() === '+') { i++; return unary(); } return power(); };
    const power = () => { const b = atom(); if (peek() === '^') { i++; return Math.pow(b, unary()); } return b; };
    const atom = () => {
      const t = toks[i++];
      if (t === undefined) throw fail(400, 'İfade eksik');
      if (/^\d/.test(t)) return Number(t);
      if (t === '(') { const v = expr(); eat(')'); return v; }
      if (/^[a-zA-Z]+$/.test(t)) {
        const k = t.toLowerCase();
        if (peek() === '(') {
          if (!FN[k]) throw fail(400, `Bilinmeyen fonksiyon: ${t}`);
          i++; const args = [];
          if (peek() !== ')') { args.push(expr()); while (peek() === ',') { i++; args.push(expr()); } }
          eat(')');
          return FN[k](...args);
        }
        if (k in CONST) return CONST[k];
        throw fail(400, `Bilinmeyen ifade: ${t}`);
      }
      throw fail(400, `Beklenmeyen: ${t}`);
    };
    const v = expr();
    if (i < toks.length) throw fail(400, `İfade hatalı: "${toks[i]}"`);
    if (!Number.isFinite(v)) throw fail(400, 'Sonuç hesaplanamadı (sıfıra bölme veya tanımsız işlem)');
    return v;
  }
  function hesapla(_, ctx) {
    const raw = (ctx.rest.length ? ctx.rest.map(dec).join('/') : ctx.q('ifade') || ctx.q('q') || '').trim();
    if (!raw) throw fail(400, 'Kullanım: /hesapla?ifade=2*(3+4)^2. Fonksiyonlar: sqrt, abs, sin, cos, tan, log, ln, exp, round, floor, ceil, min, max, pow; sabitler: pi, e');
    if (raw.length > 300) throw fail(400, 'İfade en fazla 300 karakter olabilir');
    return { ifade: raw, sonuc: sig(evalExpr(raw)), not: 'sin/cos/tan radyan alır. % mod (kalan) işlemidir.' };
  }

  // ---- 12. /aktivite ----
  const MET = { yuruyus: ['Yürüyüş', 3.5], kosu: ['Koşu', 9.8], bisiklet: ['Bisiklet', 7.5], yuzme: ['Yüzme', 7], futbol: ['Futbol', 7], basketbol: ['Basketbol', 6.5], tenis: ['Tenis', 7.3], dans: ['Dans', 5], yoga: ['Yoga', 2.5], agirlik: ['Ağırlık çalışması', 5], merdiven: ['Merdiven çıkma', 8], ipatlama: ['İp atlama', 11], temizlik: ['Ev temizliği', 3.3], bahce: ['Bahçe işleri', 4] };
  function aktivite(_, ctx) {
    const tur = norm(seg(ctx, 0) || ctx.q('tur')).replace(/[^a-z]/g, '');
    if (!tur) return { aktiviteler: Object.entries(MET).map(([k, [ad]]) => `${k}: ${ad}`), kullanim: '/aktivite/kosu/30?kilo=70' };
    const a = MET[tur];
    if (!a) throw fail(404, 'Aktivite bulunamadı, liste için /aktivite');
    const dk = money(seg(ctx, 1) || ctx.q('dakika'), 'dakika', 1440), kilo = ctx.q('kilo') ? num(ctx.q('kilo'), 'kilo') : 70;
    if (kilo < 20 || kilo > 300) throw fail(400, 'kilo 20-300 arasında olmalı');
    return { aktivite: a[0], sure_dakika: dk, kilo, met: a[1], yakilan_kalori_kcal: Math.round((a[1] * kilo * dk) / 60), not: 'MET değerlerine göre yaklaşık hesaptır, kişiden kişiye değişir.' };
  }

  // ---- 13. /yemek ----
  const YEMEKLER = [
    ['Menemen', 'kahvalti', 15, 'yumurta, domates, yeşil biber, zeytinyağı'], ['Sahanda yumurta', 'kahvalti', 10, 'yumurta, tereyağı'],
    ['Omlet', 'kahvalti', 10, 'yumurta, peynir, süt'], ['Çılbır', 'kahvalti', 20, 'yumurta, yoğurt, sarımsak, tereyağı'], ['Pişi', 'kahvalti', 25, 'un, maya, yoğurt, sıvı yağ'],
    ['Mercimek çorbası', 'corba', 30, 'kırmızı mercimek, soğan, havuç, patates, tereyağı'], ['Ezogelin çorbası', 'corba', 40, 'kırmızı mercimek, bulgur, pirinç, soğan, salça'],
    ['Domates çorbası', 'corba', 25, 'domates, un, tereyağı, süt'], ['Yayla çorbası', 'corba', 35, 'yoğurt, pirinç, yumurta, nane'], ['Tarhana çorbası', 'corba', 15, 'tarhana, salça, tereyağı'],
    ['Karnıyarık', 'ana', 60, 'patlıcan, kıyma, soğan, domates, biber'], ['Mücver', 'ana', 30, 'kabak, yumurta, un, dereotu, peynir'], ['Tavuk sote', 'ana', 30, 'tavuk göğsü, biber, domates, soğan'],
    ['Makarna', 'ana', 15, 'makarna, salça, tereyağı, peynir'], ['Pilav', 'ana', 25, 'pirinç, tereyağı, tel şehriye'], ['Izgara köfte', 'ana', 30, 'kıyma, soğan, ekmek içi, baharat'],
    ['Fırın tavuk', 'ana', 60, 'tavuk but, patates, biber, zeytinyağı'], ['Türlü', 'ana', 50, 'patlıcan, kabak, biber, domates, patates'], ['Taze fasulye', 'ana', 45, 'fasulye, soğan, domates, zeytinyağı'],
    ['Kuru fasulye', 'ana', 90, 'kuru fasulye, soğan, salça, tereyağı'], ['Sigara böreği', 'ana', 30, 'yufka, peynir, maydanoz, sıvı yağ'], ['Patates yemeği', 'ana', 35, 'patates, soğan, domates, salça'],
    ['Ispanaklı yumurta', 'ana', 15, 'ıspanak, yumurta, soğan'], ['Nohutlu pilav', 'ana', 30, 'pirinç, nohut, tereyağı'],
    ['Çoban salatası', 'salata', 10, 'domates, salatalık, biber, soğan, maydanoz'], ['Cacık', 'salata', 10, 'yoğurt, salatalık, sarımsak, nane'], ['Piyaz', 'salata', 20, 'kuru fasulye, soğan, maydanoz, zeytinyağı'],
    ['Havuç salatası', 'salata', 10, 'havuç, yoğurt, sarımsak'],
    ['Sütlaç', 'tatli', 50, 'süt, pirinç, şeker, nişasta'], ['Revani', 'tatli', 45, 'irmik, yumurta, şeker, yoğurt'], ['Kek', 'tatli', 45, 'un, yumurta, şeker, süt, kabartma tozu'],
    ['Puding', 'tatli', 20, 'süt, şeker, nişasta, kakao'], ['Muhallebi', 'tatli', 20, 'süt, şeker, nişasta, pirinç unu'], ['Meyve salatası', 'tatli', 10, 'mevsim meyveleri, bal'],
  ];
  function yemek(_, ctx) {
    const ogun = norm(seg(ctx, 0) || ctx.q('ogun')).replace(/[^a-z]/g, '');
    const ogunler = ['kahvalti', 'corba', 'ana', 'salata', 'tatli'];
    if (ogun && !ogunler.includes(ogun)) throw fail(400, `ogun: ${ogunler.join(', ')}`);
    const mal = (ctx.q('malzeme') || '').split(',').map((x) => norm(x)).filter(Boolean).slice(0, 8);
    let list = YEMEKLER.filter((y) => (!ogun || y[1] === ogun) && mal.every((m) => norm(y[3]).includes(m)));
    if (!list.length) throw fail(404, 'Bu şartlara uyan yemek bulunamadı');
    const n = clamp(int(ctx.q('adet'), 1), 1, 5);
    return { oneriler: shuffle(list).slice(0, n).map((y) => ({ yemek: y[0], ogun: y[1], sure_dk: y[2], malzemeler: y[3] })), kullanim: '/yemek/ana?malzeme=patates,soğan', ogunler };
  }

  // ---- 14. /giyim ----
  async function giyim(_, ctx) {
    const name = cityArg(ctx, 'giyim');
    const w = await hava(null, { rest: [name], q: (k) => (k === 'ulke' ? ctx.q('ulke') : null) });
    const s = w.simdi, t = s.hissedilen_c ?? s.sicaklik_c, today = w.tahmin?.[0] || {};
    let ust = t <= 0 ? 'Kalın mont, bere, eldiven ve atkı' : t <= 8 ? 'Mont ve kalın kazak' : t <= 15 ? 'Ceket veya hırka, uzun pantolon' : t <= 22 ? 'İnce ceket ya da uzun kollu üst' : t <= 28 ? 'Tişört ve hafif pantolon veya şort' : 'İnce, açık renkli kıyafetler ve şapka';
    const ek = [];
    if ((today.yagis_ihtimali_yuzde ?? 0) >= 50 || s.yagis_mm > 0) ek.push('Şemsiye veya yağmurluk');
    if ((s.ruzgar_kmh ?? 0) >= 30) ek.push('Rüzgarlık');
    if (t >= 25) ek.push('Güneş kremi ve bol su');
    return { konum: w.konum, durum: s.durum, sicaklik_c: s.sicaklik_c, hissedilen_c: s.hissedilen_c, oneri: ust, ek_oneriler: ek.length ? ek : ['Yok'], bugun_en_dusuk_c: today.en_dusuk_c, bugun_en_yuksek_c: today.en_yuksek_c };
  }

  // ---- 15. /varis ----
  function varis(_, ctx) {
    const km = money(seg(ctx, 0) || ctx.q('km'), 'km', 50000), hiz = money(seg(ctx, 1) || ctx.q('hiz'), 'hiz (km/s)', 1500);
    if (!km || !hiz) throw fail(400, 'Kullanım: /varis/{km}/{hiz}?saat=08:30&mola=15');
    const mola = ctx.q('mola') ? clamp(Math.trunc(num(ctx.q('mola'), 'mola')), 0, 120) : 15;
    const driveMin = Math.round((km / hiz) * 60), breaks = Math.floor(driveMin / 120) * mola, total = driveMin + breaks;
    let startMin;
    const sv = ctx.q('saat');
    if (sv) { const m = sv.match(/^(\d{1,2}):(\d{2})$/); if (!m || +m[1] > 23 || +m[2] > 59) throw fail(400, 'saat HH:MM biçiminde olmalı'); startMin = +m[1] * 60 + +m[2]; }
    else { const n = new Date(Date.now() + 3 * 36e5); startMin = n.getUTCHours() * 60 + n.getUTCMinutes(); }
    const endAbs = startMin + total;
    return { mesafe_km: km, ortalama_hiz_kmh: hiz, surus_suresi: `${Math.floor(driveMin / 60)} sa ${driveMin % 60} dk`, mola_toplam_dk: breaks, toplam_sure: `${Math.floor(total / 60)} sa ${total % 60} dk`, cikis_saati: hhmm(startMin), varis_saati: hhmm(endAbs), gun_farki: Math.floor(endAbs / 1440), not: `Her 2 saatlik sürüşe ${mola} dk mola eklenir.` };
  }

  // ---- 16. /zekat ----
  function zekat(_, ctx) {
    const varlik = money(pathOrQuery(ctx, 0, 'varlik'), 'varlik', 1e13);
    if (!ctx.q('nisap')) throw fail(400, 'nisap gerekli: 80.18 gram altının güncel TL karşılığı (örn. ?nisap=250000)');
    const nisap = num(ctx.q('nisap'), 'nisap'), borc = ctx.q('borc') ? money(ctx.q('borc'), 'borc', 1e13) : 0;
    const net = Math.max(0, varlik - borc);
    return { varlik, borc, net_varlik: r2(net), nisap, zekat_gerekir: net >= nisap, zekat_tutari: net >= nisap ? r2(net * 0.025) : 0, oran: '%2.5', not: 'Hesap bilgilendirme amaçlıdır. Hawl (bir yıl) şartı ve dini hükümler için yetkili kurumlara danışın.' };
  }

  // ---- 17. /etkilesim (bot komutları) ----
  const VOW = 'aeıioöuü';
  const lastVowel = (w) => { const s = trLower(w); for (let i = s.length - 1; i >= 0; i--) if (VOW.includes(s[i])) return s[i]; return 'e'; };
  function suffix(w, kind) {
    const v = lastVowel(w), buf = VOW.includes(trLower(w).slice(-1)) ? 'y' : '';
    const s = kind === 'acc' ? ('aı'.includes(v) ? 'ı' : 'ou'.includes(v) ? 'u' : 'ei'.includes(v) ? 'i' : 'ü') : ('aıou'.includes(v) ? 'a' : 'e');
    return `${w}'${buf}${s}`;
  }
  const ACTIONS = {
    op: { gif: 'kiss', acc: (a, b) => `${a}, ${suffix(b, 'acc')} öptü.`, solo: (a) => `${a} havaya öpücük gönderdi.` },
    saril: { gif: 'hug', dat: (a, b) => `${a}, ${suffix(b, 'dat')} sarıldı.`, solo: (a) => `${a} kendine sarıldı.` },
    tokat: { gif: 'slap', dat: (a, b) => `${a}, ${suffix(b, 'dat')} tokat attı.`, solo: (a) => `${a} kendi yüzüne tokat attı.` },
    elsik: { gif: 'handshake', fn: (a, b) => `${a}, ${b} ile el sıkıştı.`, solo: (a) => `${a} kendi eliyle el sıkıştı.` },
    selam: { gif: 'wave', dat: (a, b) => `${a}, ${suffix(b, 'dat')} selam verdi.`, solo: (a) => `${a} herkese selam verdi.` },
    dans: { gif: 'dance', fn: (a, b) => `${a}, ${b} ile dans etti.`, solo: (a) => `${a} tek başına dans etti.` },
    agla: { gif: 'cry', fn: (a, b) => `${a}, ${b} yüzünden ağlıyor.`, solo: (a) => `${a} ağlıyor.` },
    gul: { gif: 'laugh', dat: (a, b) => `${a}, ${suffix(b, 'dat')} güldü.`, solo: (a) => `${a} güldü.` },
    alkis: { gif: 'clap', acc: (a, b) => `${a}, ${suffix(b, 'acc')} alkışladı.`, solo: (a) => `${a} alkışladı.` },
    durt: { gif: 'poke', acc: (a, b) => `${a}, ${suffix(b, 'acc')} dürttü.`, solo: (a) => `${a} kendini dürttü.` },
    oksa: { gif: 'pat', acc: (a, b) => `${a}, ${suffix(b, 'acc')} okşadı.`, solo: (a) => `${a} kendini okşadı.` },
  };
  const ACT_ALIAS = { opucuk: 'op', sarilma: 'saril', sarila: 'saril', elsikis: 'elsik', selamla: 'selam', alkisla: 'alkis', dursu: 'durt', oksama: 'oksa', gulme: 'gul', aglama: 'agla', danset: 'dans' };
  async function etkilesim(_, ctx) {
    const raw = norm(seg(ctx, 0) || ctx.q('eylem')).replace(/[^a-z]/g, '');
    if (!raw) return { eylemler: Object.keys(ACTIONS), kullanim: '/etkilesim/op?kim=Ahmet&kime=Ayşe&gif=1' };
    const key = ACT_ALIAS[raw] || raw, a = ACTIONS[key];
    if (!a) throw fail(404, `Eylem bulunamadı. Eylemler: ${Object.keys(ACTIONS).join(', ')}`);
    const kim = cleanName(ctx.q('kim'), 'kim') || 'Biri', kime = cleanName(ctx.q('kime'), 'kime');
    const mesaj = kime ? (a.acc || a.dat || a.fn)(kim, kime) : a.solo(kim);
    const out = { eylem: key, mesaj };
    if (wantsTrue(ctx.q('gif'))) {
      try {
        const j = await fetchJson(`https://nekos.best/api/v2/${a.gif}`, { headers: UA }, 'Gif servisine ulaşılamadı');
        out.gif = j?.results?.[0]?.url || null;
      } catch { out.gif = null; out.gif_notu = 'Gif servisine şu an ulaşılamadı'; }
    }
    return out;
  }

  // ---- 18. /ship ----
  function ship(_, ctx) {
    const a = cleanName(seg(ctx, 0) || ctx.q('a'), 'isim 1'), b = cleanName(seg(ctx, 1) || ctx.q('b'), 'isim 2');
    if (!a || !b) throw fail(400, 'Kullanım: /ship/{isim1}/{isim2}');
    const yuzde = hashInt([norm(a), norm(b)].sort().join('|')) % 101;
    const yorum = yuzde < 20 ? 'Pek uyumlu görünmüyor, ama kalpler şaşırtır.' : yuzde < 40 ? 'Biraz çaba gerekir.' : yuzde < 60 ? 'Fena değil, anlaşabilirler.' : yuzde < 80 ? 'Güzel bir uyum var.' : 'Mükemmel uyum.';
    const A = Array.from(a), B = Array.from(b);
    return { isim1: a, isim2: b, uyum_yuzde: yuzde, cubuk: '#'.repeat(Math.round(yuzde / 10)) + '-'.repeat(10 - Math.round(yuzde / 10)), yorum, ship_adi: A.slice(0, Math.ceil(A.length / 2)).join('') + B.slice(Math.floor(B.length / 2)).join(''), not: 'Eğlence amaçlıdır. Aynı isim çifti her zaman aynı sonucu verir.' };
  }

  // ---- 19. /8top ----
  const SEKIZ = {
    olumlu: ['Kesinlikle evet.', 'Evet, öyle görünüyor.', 'Bence evet.', 'Büyük ihtimalle.', 'İşaretler olumlu.', 'Hiç şüphen olmasın.', 'Evet, devam et.', 'Şansın yüksek.', 'Güvenebilirsin.', 'Olacak gibi.'],
    belirsiz: ['Şimdi net değil, tekrar sor.', 'Daha sonra tekrar dene.', 'Şu an söylememek daha iyi.', 'İçinden geçeni dinle ve tekrar sor.', 'Konsantre ol ve yeniden sor.'],
    olumsuz: ['Bence hayır.', 'Pek sanmıyorum.', 'Cevabım hayır.', 'Kaynaklarım hayır diyor.', 'Çok şüpheli.'],
  };
  function sekiztop(_, ctx) {
    const soru = clip(ctx.q('soru') || ctx.rest.map(dec).join(' '), 200, 'soru');
    const tip = ['olumlu', 'olumlu', 'belirsiz', 'olumsuz'][randomInt(0, 4)];
    return { soru: soru || null, cevap: pick(SEKIZ[tip]), tur: tip };
  }

  // ---- 20. /dogruluk-cesaret ----
  const DOGRULUK = {
    hafif: ['En sevdiğin yemek nedir?', 'Çocukken ne olmak isterdin?', 'Telefonunda en çok kullandığın uygulama hangisi?', 'Hiç yapmadığın ama yapmak istediğin bir şey nedir?', 'Sabah mı gece mi? Neden?'],
    orta: ['Son aldığın en gereksiz şey neydi?', 'Kimseye söylemediğin küçük bir alışkanlığın var mı?', 'Bir gün için başka biri olsan kim olurdun?', 'Hayatındaki en utandırıcı anı anlat.', 'En son ne zaman yalan söyledin?'],
    eglenceli: ['Tek bir süper gücün olsa ne olurdu?', 'Issız adaya üç şey götürebilsen ne götürürdün?', 'En komik rüyanı anlat.', 'Bir hayvan olsan hangisi olurdun?', 'Hiç duşta şarkı söyler misin, hangi şarkıyı?'],
  };
  const CESARET = {
    hafif: ['Bir dakika boyunca hiç gülme.', 'En sevdiğin şarkıdan bir dize söyle.', 'Yan tarafındakine iltifat et.', 'Sıfatsız bir cümle kur.', 'Beş zıplama yap.'],
    orta: ['Grup sohbetine komik bir selfie gönder.', 'Bir hayvanı taklit et, diğerleri tahmin etsin.', 'Bir dakika boyunca robot gibi konuş.', 'Telefonundaki son fotoğrafı göster.', 'Kendine yeni bir lakap bul ve bir saat boyunca kullan.'],
    eglenceli: ['Tek ayak üstünde 30 saniye dur.', 'Alfabeyi tersten söylemeyi dene.', 'Ağzında kalemle bir cümle söyle.', 'Duyduğun ilk şarkıya dans et.', 'Bir tavuk gibi ötmeyi dene.'],
  };
  function dogrulukcesaret(_, ctx) {
    const tur = norm(seg(ctx, 0) || ctx.q('tur')).replace(/[^a-z]/g, '') || pick(['dogruluk', 'cesaret']);
    if (!['dogruluk', 'cesaret'].includes(tur)) throw fail(400, 'tur: dogruluk veya cesaret');
    const sev = norm(ctx.q('seviye')).replace(/[^a-z]/g, '') || pick(['hafif', 'orta', 'eglenceli']);
    const set = tur === 'dogruluk' ? DOGRULUK : CESARET;
    if (!set[sev]) throw fail(400, 'seviye: hafif, orta veya eglenceli');
    return { tur, seviye: sev, icerik: pick(set[sev]) };
  }

  // ---- 21. /fal ----
  const FAL = {
    genel: ['Bugün küçük bir sürpriz seni bekliyor.', 'Yeni bir fırsat kapını çalabilir, hazırlıklı ol.', 'Sabırlı olursan bekleyişin karşılığını alırsın.', 'Eski bir dostun haber verebilir.', 'Bugün kararlarını sezgilerinle ver.', 'Küçük bir değişiklik büyük bir fark yaratacak.', 'Etrafındaki iyi niyetli insanları fark edeceksin.', 'Bir plan yapmak için uygun bir gün.'],
    ask: ['Kalbin bugün yumuşak, kendine zaman tanı.', 'Beklenmedik bir mesaj kalbini ısıtabilir.', 'Açık yürekli bir konuşma bir şeyleri çözecek.', 'Eski bir hatıra gülümsetecek.', 'Sevdiklerine zaman ayırmak seni mutlu eder.', 'Yeni biriyle karşılaşma ihtimalin yüksek.'],
    para: ['Harcamalarında temkinli olmak iyi gelir.', 'Beklediğin bir ödeme bugün netleşebilir.', 'Küçük bir tasarruf sonra işine yarayacak.', 'Büyük kararları bugün ertelemek akıllıca.', 'Bir yan gelir fikri aklına gelebilir.', 'Planlı davranmak seni rahatlatacak.'],
    saglik: ['Bol su iç ve biraz yürü.', 'Bugün erken yatmak sana iyi gelecek.', 'Kendine bir mola ver, nefes al.', 'Hareket etmek enerjini yükseltir.', 'Dengeli beslenmek seni toparlar.', 'Stresi yavaşlatan küçük bir ritüel bul.'],
    renk: ['Mavi', 'Yeşil', 'Turuncu', 'Mor', 'Kırmızı', 'Sarı', 'Beyaz', 'Lacivert'],
    kahve: ['Fincanda bir yol görünüyor, yakında küçük bir yolculuk ya da haber var.', 'Fincanın ortasında bir kuş var, güzel bir haber yolda.', 'Kenarda bir halka görünüyor, sevdiklerinle bağın güçlenecek.', 'Fincanın dibinde bir anahtar var, bir kapı açılacak.', 'Bir dağ silueti var, engeller aşılacak.', 'Bir balık görünüyor, bereket ve şans seni bulacak.'],
  };
  function fal(_, ctx) {
    const b = norm(seg(ctx, 0) || ctx.q('burc')).replace(/[^a-z]/g, '');
    if (!b) return { tur: 'kahve falı', fal: pick(FAL.kahve), not: 'Eğlence amaçlıdır. Burcunuzu yazarsanız günlük fal: /fal/koc' };
    const sign = SIGNS.find((s) => norm(s[0]) === b);
    if (!sign) throw fail(404, `Burç bulunamadı: ${SIGNS.map((s) => norm(s[0])).join(', ')}`);
    const day = isoMs(trToday());
    const h = (k) => hashInt(`${day}|${sign[0]}|${k}`);
    return { burc: sign[0], tarih: day, genel: FAL.genel[h('g') % FAL.genel.length], ask: FAL.ask[h('a') % FAL.ask.length], para: FAL.para[h('p') % FAL.para.length], saglik: FAL.saglik[h('s') % FAL.saglik.length], sans_sayisi: (h('n') % 99) + 1, sans_rengi: FAL.renk[h('r') % FAL.renk.length], not: 'Eğlence amaçlıdır. Aynı gün aynı burç aynı sonucu alır.' };
  }

  // ---- 22. /iltifat ----
  const ILTIFAT = ['Gülüşün odayı aydınlatıyor.', 'Çok zekisin, konuşmaların hep ilham veriyor.', 'Yanında olmak insana iyi geliyor.', 'Yaptığın işi gerçekten çok güzel yapıyorsun.', 'Enerjin bulaşıcı, herkes seninle iyi hissediyor.', 'Sabrın ve nezaketin takdire değer.', 'Mizah anlayışın harika.', 'Çok çalışkansın ve bunu herkes görüyor.', 'İyi ki varsın.', 'Bir sorunu çözüş şeklin hayranlık uyandırıyor.', 'Güvenilir biri olduğun çok belli.', 'Fikirlerin hep özgün.', 'Kalbin çok büyük.', 'Seninle sohbet etmek çok keyifli.', 'Başardığın her şey seni daha da güçlü yapıyor.', 'Stilin çok hoş.', 'Verdiğin destek herkese iyi geliyor.', 'Kendi yolunu çizmen çok değerli.', 'Gülümsemen bulaşıcı.', 'Bugün de harika görünüyorsun.'];
  function iltifat(_, ctx) {
    const isim = cleanName(seg(ctx, 0) || ctx.q('isim'), 'isim'), m = pick(ILTIFAT);
    return { iltifat: isim ? `${isim}, ${trLower(Array.from(m)[0])}${Array.from(m).slice(1).join('')}` : m };
  }

  // ---- 23. /espri ----
  const ESPRILER = [
    'Matematik kitabı neden üzgün? Çünkü çok problemi var.', 'Takvim neden popülerdi? Çünkü herkesin günleri onda sayılıydı.', 'Kahve neden polise gitti? Çünkü biri onu ezmişti.', 'Balık neden okula gitmez? Çünkü zaten hep sürüdedir ve ders çalışmaya vakti yoktur.', 'Bilgisayar neden üşümez? Çünkü hep penceresi açıktır.',
    'Telefonum neden hep şarjda? Çünkü bağımlılık yapan bir ilişkimiz var.', 'Saat neden iyi arkadaştır? Çünkü her zaman yanında olur ve vaktini ayırır.', 'Kalem silgiye ne demiş? Beni hep geri alıyorsun.', 'Pilot neden sakin? Çünkü her şey yolunda gidiyor, rotası belli.', 'Ağaç neden internete bağlanmaz? Çünkü zaten dalları geniş ağ.',
    'Pasta neden mutlu? Çünkü herkesin onu bekleyen biri var.', 'Çay neden hızlı soğur? Çünkü sohbete dalarsan unutulur.', 'Kitap neden iyi dinleyicidir? Çünkü sayfaları hep ağzı kapalıdır.', 'Elma neden ağaçtan düştü? Çünkü yerçekimi ona haber vermedi.', 'Bulut neden ağlar? Çünkü yağmur olma vakti gelmiştir.',
    'Güneş neden gözlük takar? Çünkü geleceği çok parlak.', 'Klavye neden yorgun? Çünkü bütün gün tuşları sıkıyor.', 'Müzisyen neden sakin? Çünkü her şeyi notaya bağlar.', 'Telefon neden zeki? Çünkü hep akıllı olmaya çalışıyor.', 'Kedi neden bilgisayar sever? Çünkü fare orada.',
  ];
  const FIKRALAR = [
    'Nasreddin Hoca bir gün göle maya çalıyormuş. Görenler "Hocam ne yapıyorsun?" demiş. Hoca "Göl yoğurt olur mu diye deniyorum" demiş. "Hiç olur mu?" diyenlere "Ya tutarsa?" diye cevap vermiş.',
    'Nasreddin Hoca bir gün eşeğine ters binmiş. Sebebini soranlara "Ben eşeğin yüzüne bakmayayım diye değil, eşek bana bakmasın diye böyle biniyorum" demiş.',
    'Hoca\'nın komşusu ödünç bir kazan istemiş. Hoca kazanı verince komşu bir küçük kazan daha getirmiş ve "Kazan doğurdu" demiş. Bir süre sonra Hoca kazanı geri vermemiş ve "Kazan öldü" demiş. Komşu itiraz edince "Doğuran ölmez mi?" cevabını vermiş.',
    'Nasreddin Hoca camiye giderken birisi "Hocam, kaç yaşındasınız?" diye sormuş. Hoca "Kırk" demiş. Bir yıl sonra aynı kişi sorunca yine "Kırk" cevabını vermiş. "Geçen yıl da kırktı" denince "Ben lafımın arkasındayım" demiş.',
    'Nasreddin Hoca\'ya "Dünyanın ortası neresi?" diye sormuşlar. Hoca eşeğinin ön ayağını gösterip "Tam şurası, inanmazsanız ölçün" demiş.',
    'Nasreddin Hoca bir düğüne eski kıyafetlerle gitmiş, kimse ilgilenmemiş. Eve gidip en güzel kürkünü giyerek dönmüş ve herkes ilgi göstermiş. Hoca kürkünün yenine yemek dökerek "Ye kürküm ye, davet sana yapılmış" demiş.',
  ];
  function espri(_, ctx) {
    const tur = norm(seg(ctx, 0) || ctx.q('tur')).replace(/[^a-z]/g, '') || 'espri';
    if (!['espri', 'fikra'].includes(tur)) throw fail(400, 'tur: espri veya fikra');
    return { tur, metin: pick(tur === 'espri' ? ESPRILER : FIKRALAR) };
  }

  // ---- 24. /bilmece ----
  const BILMECELER = [
    ['Ne kadar çok alırsan o kadar çok bırakırsın.', 'Adım'], ['Her gün seni izler ama gözü yoktur, ışıkla gelir ışıkla gider.', 'Gölge'], ['Dişi çoktur ama ısırmaz, saçlarımızı düzene sokar.', 'Tarak'],
    ['Gökten düşer ama canı yanmaz.', 'Yağmur'], ['Tuşları var ama daktilo değil, notalar onunla konuşur.', 'Piyano'], ['Yüzü var, elleri var, durmadan koşar ama yerinden ayrılmaz.', 'Saat'],
    ['Sayfaları çok, konuşmaz ama bilgi verir.', 'Kitap'], ['Geceleri parlar, gündüz kaybolur, bazen yarım bazen tam olur.', 'Ay'], ['Yağmurda açılır, güneşte kapanır.', 'Şemsiye'],
    ['Cebimde taşırım, kilidi açarım.', 'Anahtar'], ['Üstünde yürürsün ama dönüp bakmaz, her adımda seni taşır.', 'Yol'], ['Kuyruğu var ama tüyü yok, delikten geçer, sökükleri diker.', 'İğne'],
    ['Karnı hep boştur, para atarsan doyar.', 'Kumbara'], ['Yazdıkça boyu kısalır.', 'Kalem'], ['Suyun üstünde gezer, rüzgarla yol alır.', 'Yelkenli'],
    ['Dört ayağı var yürümez, üstünde yemek yenir.', 'Masa'], ['Beyaz yağar, çocukları sevindirir, eriyince kaybolur.', 'Kar'], ['Baharda açar, tatlı kokar, dikeni de vardır.', 'Gül'],
    ['Boynu direk gibi, benekli, yaprakları yüksekten yer.', 'Zürafa'],
  ];
  function bilmece(_, ctx) {
    const [soru, cevap] = pick(BILMECELER);
    return wantsTrue(ctx.q('gizle')) ? { bilmece: soru, cevap_uzunlugu: Array.from(cevap).length, ilk_harf: Array.from(cevap)[0] } : { bilmece: soru, cevap, cevap_uzunlugu: Array.from(cevap).length };
  }

  // ---- 25. /quiz ----
  const QUIZ = {
    cografya: [
      ['Türkiye\'nin başkenti neresidir?', ['Ankara', 'İstanbul', 'İzmir', 'Bursa'], 0], ['Türkiye\'nin en yüksek dağı hangisidir?', ['Erciyes', 'Ağrı Dağı', 'Uludağ', 'Kaçkar'], 1],
      ['Sınırları içinde en uzun nehrimiz hangisidir?', ['Sakarya', 'Fırat', 'Kızılırmak', 'Yeşilırmak'], 2], ['Hangisi bir kıta değildir?', ['Asya', 'Okyanusya', 'Grönland', 'Afrika'], 2],
      ['Dünyanın en büyük okyanusu hangisidir?', ['Atlas', 'Hint', 'Pasifik', 'Arktik'], 2], ['Nil Nehri hangi kıtadadır?', ['Asya', 'Afrika', 'Avrupa', 'Güney Amerika'], 1], ['Japonya\'nın başkenti neresidir?', ['Osaka', 'Kyoto', 'Tokyo', 'Seul'], 2],
    ],
    tarih: [
      ['Türkiye Cumhuriyeti hangi yılda ilan edildi?', ['1920', '1923', '1938', '1919'], 1], ['İstanbul hangi yılda fethedildi?', ['1453', '1299', '1071', '1517'], 0], ['Malazgirt Savaşı hangi yıl yapıldı?', ['1071', '1176', '1402', '1453'], 0],
      ['Çanakkale Deniz Zaferi hangi yıldır?', ['1912', '1915', '1918', '1920'], 1], ['Mustafa Kemal Atatürk Kurtuluş Savaşı için 19 Mayıs 1919\'da hangi şehre çıktı?', ['İzmir', 'Ankara', 'Samsun', 'Sivas'], 2], ['Osmanlı Devleti\'nin kurucusu kimdir?', ['Orhan Bey', 'Osman Bey', 'Ertuğrul Gazi', 'Murat Hüdavendigar'], 1],
    ],
    genel: [
      ['Güneş sisteminin en büyük gezegeni hangisidir?', ['Satürn', 'Jüpiter', 'Mars', 'Neptün'], 1], ['Suyun kimyasal formülü nedir?', ['CO2', 'O2', 'H2O', 'NaCl'], 2], ['Işığın hızı yaklaşık kaç km/s\'dir?', ['30.000', '300.000', '3.000.000', '150.000'], 1],
      ['Futbolda sahada bir takımda kaç oyuncu bulunur?', ['9', '10', '11', '12'], 2], ['Kızıl Gezegen hangisidir?', ['Venüs', 'Mars', 'Merkür', 'Uranüs'], 1], ['Yetişkin insanda kaç kemik vardır?', ['106', '206', '306', '406'], 1],
      ['Standart bir piyanoda kaç tuş vardır?', ['66', '76', '88', '98'], 2], ['En hızlı kara hayvanı hangisidir?', ['Aslan', 'Çita', 'At', 'Tavşan'], 1], ['Mona Lisa tablosunu kim yapmıştır?', ['Michelangelo', 'Van Gogh', 'Leonardo da Vinci', 'Picasso'], 2], ['Altının sembolü nedir?', ['Ag', 'Au', 'Fe', 'Cu'], 1],
    ],
  };
  function quiz(_, ctx) {
    const kat = norm(seg(ctx, 0) || ctx.q('kategori')).replace(/[^a-z]/g, '');
    if (kat && !QUIZ[kat]) throw fail(400, `kategori: ${Object.keys(QUIZ).join(', ')}`);
    const key = kat || pick(Object.keys(QUIZ)), [soru, opts, ans] = pick(QUIZ[key]);
    const order = shuffle([0, 1, 2, 3]), secenekler = order.map((i) => opts[i]), dogru = order.indexOf(ans);
    const out = { kategori: key, soru, secenekler: secenekler.map((o, i) => `${'ABCD'[i]}) ${o}`) };
    if (!wantsTrue(ctx.q('gizle'))) { out.dogru_harf = 'ABCD'[dogru]; out.dogru_cevap = secenekler[dogru]; }
    return out;
  }

  // ---- 26. /adamasmaca ----
  const ADAM = [['kedi', 'hayvan'], ['elma', 'meyve'], ['masa', 'eşya'], ['deniz', 'doğa'], ['araba', 'taşıt'], ['çiçek', 'bitki'], ['kitap', 'eşya'], ['güneş', 'gökyüzü'], ['bulut', 'doğa'], ['tavuk', 'hayvan'], ['limon', 'meyve'], ['kalem', 'eşya'],
    ['bisiklet', 'taşıt'], ['mutfak', 'ev'], ['öğretmen', 'meslek'], ['penguen', 'hayvan'], ['ayakkabı', 'giysi'], ['pencere', 'ev'], ['çikolata', 'yiyecek'], ['bahçıvan', 'meslek'], ['kelebek', 'hayvan'], ['merdiven', 'ev'], ['mercimek', 'yiyecek'],
    ['kütüphane', 'yer'], ['bilgisayar', 'eşya'], ['helikopter', 'taşıt'], ['denizaltı', 'taşıt'], ['televizyon', 'eşya'], ['kaplumbağa', 'hayvan'], ['mühendislik', 'meslek'], ['ayçiçeği', 'bitki'], ['havalimanı', 'yer'], ['kahvaltı', 'yiyecek']];
  function adamasmaca(_, ctx) {
    const z = norm(seg(ctx, 0) || ctx.q('zorluk')).replace(/[^a-z]/g, '');
    if (z && !['kolay', 'orta', 'zor'].includes(z)) throw fail(400, 'zorluk: kolay, orta veya zor');
    const len = (w) => Array.from(w).length;
    const list = ADAM.filter(([w]) => !z || (z === 'kolay' ? len(w) <= 5 : z === 'orta' ? len(w) >= 6 && len(w) <= 8 : len(w) >= 9));
    const [kelime, ipucu] = pick(list), n = len(kelime);
    return { zorluk: n <= 5 ? 'kolay' : n <= 8 ? 'orta' : 'zor', harf_sayisi: n, ipucu, maske: Array(n).fill('_').join(' '), hak: 6, ...(wantsTrue(ctx.q('gizle')) ? {} : { kelime: trUpper(kelime) }) };
  }

  // ---- 27. /wordle ----
  const WORDLE = ['kalem', 'kitap', 'masal', 'bahar', 'deniz', 'çiçek', 'sevgi', 'hayat', 'dünya', 'bulut', 'aslan', 'tilki', 'kuzey', 'güney', 'yazar', 'şehir', 'köprü', 'çocuk', 'saray', 'vapur', 'tarla', 'orman', 'kumru', 'karga', 'balık', 'insan', 'parça', 'zaman', 'melek', 'ejder', 'dolap', 'pasta', 'sabah', 'akşam', 'tahta', 'takım', 'ceket', 'koyun', 'sebze', 'meyve', 'şeker', 'tuzlu', 'ekmek', 'sınıf', 'kıyas', 'lokum', 'yağız', 'güzel'].filter((w) => Array.from(w).length === 5);
  function wordle(_, ctx) {
    const dayNo = Math.floor(trToday() / 864e5);
    const gunluk = wantsTrue(ctx.q('gunluk')), w = gunluk ? WORDLE[dayNo % WORDLE.length] : pick(WORDLE);
    const tah = ctx.q('tahmin');
    const out = { harf_sayisi: 5, ...(gunluk ? { gun: isoMs(trToday()) } : {}) };
    if (tah) {
      const g = Array.from(trLower(tah.trim())), t = Array.from(w);
      if (g.length !== 5) throw fail(400, 'tahmin 5 harfli olmalı');
      const res = Array(5).fill('yok'), left = {};
      t.forEach((c, i) => { if (g[i] === c) res[i] = 'dogru'; else left[c] = (left[c] || 0) + 1; });
      g.forEach((c, i) => { if (res[i] !== 'dogru' && left[c] > 0) { res[i] = 'var'; left[c]--; } });
      out.tahmin = g.join('');
      out.sonuc = res;
      out.ozet = res.map((r) => (r === 'dogru' ? 'D' : r === 'var' ? 'V' : 'Y')).join('');
      out.kazandi = res.every((r) => r === 'dogru');
      out.not = 'D: doğru yerde, V: kelimede var ama yeri yanlış, Y: yok. Günlük kelimeyi görmek için tahmin yapmadan kelimeyi bot tarafında saklayın.';
      if (!gunluk) out.kelime = trUpper(w);
    } else out.kelime = trUpper(w);
    return out;
  }

  // ---- 28. /tkm ----
  function tkm(_, ctx) {
    const MAP = { tas: 'tas', kagit: 'kagit', makas: 'makas' }, NAME = { tas: 'Taş', kagit: 'Kağıt', makas: 'Makas' };
    const h = MAP[norm(seg(ctx, 0) || ctx.q('hamle')).replace(/[^a-z]/g, '')];
    if (!h) throw fail(400, 'hamle: tas, kagit veya makas (örn. /tkm/tas)');
    const bot = pick(Object.keys(MAP)), beats = { tas: 'makas', kagit: 'tas', makas: 'kagit' };
    return { senin_hamlen: NAME[h], botun_hamlesi: NAME[bot], sonuc: h === bot ? 'Berabere' : beats[h] === bot ? 'Sen kazandın' : 'Bot kazandı' };
  }

  // ---- 29. /kart ----
  const SUITS = ['Maça', 'Kupa', 'Karo', 'Sinek'];
  const RANKN = { 11: 'Vale', 12: 'Kız', 13: 'Papaz', 14: 'As' };
  const cardName = (c) => `${SUITS[c.s]} ${RANKN[c.r] || c.r}`;
  function pokerName(cards) {
    const ranks = cards.map((c) => c.r).sort((a, b) => b - a), flush = cards.every((c) => c.s === cards[0].s);
    const cnt = {};
    ranks.forEach((r) => { cnt[r] = (cnt[r] || 0) + 1; });
    const g = Object.values(cnt).sort((a, b) => b - a), uniq = new Set(ranks).size === 5;
    const wheel = uniq && ranks.join() === '14,5,4,3,2', straight = uniq && (ranks[0] - ranks[4] === 4 || wheel);
    if (straight && flush) return ranks[0] === 14 && ranks[1] === 13 ? 'Royal Flush' : 'Düz Renk (Straight Flush)';
    if (g[0] === 4) return 'Kare (Dörtlü)';
    if (g[0] === 3 && g[1] === 2) return 'Full House';
    if (flush) return 'Renk (Flush)';
    if (straight) return 'Seri (Straight)';
    if (g[0] === 3) return 'Üçlü';
    if (g[0] === 2 && g[1] === 2) return 'İki Çift';
    if (g[0] === 2) return 'Çift';
    return 'Yüksek Kart';
  }
  function kart(_, ctx) {
    const deck = [];
    for (let s = 0; s < 4; s++) for (let r = 2; r <= 14; r++) deck.push({ s, r });
    const poker = norm(seg(ctx, 0) || ctx.q('oyun')) === 'poker';
    const n = poker ? 5 : clamp(int(ctx.q('adet'), 1), 1, 52), drawn = shuffle(deck).slice(0, n);
    return { cekilen: drawn.map(cardName), adet: n, ...(poker ? { el: pokerName(drawn) } : {}), kullanim: '/kart?adet=5 veya /kart/poker' };
  }

  // ---- 30. /takmaad ----
  const SIFAT = ['Gölge', 'Kızıl', 'Sessiz', 'Çılgın', 'Karanlık', 'Altın', 'Demir', 'Gizemli', 'Hızlı', 'Vahşi', 'Kutup', 'Gümüş', 'Alev', 'Buz', 'Yalnız', 'Kara', 'Mavi', 'Fırtına'];
  const ISIM = ['Kurt', 'Kartal', 'Ejder', 'Şahin', 'Aslan', 'Yıldırım', 'Savaşçı', 'Avcı', 'Gezgin', 'Kaplan', 'Akrep', 'Tilki', 'Şövalye', 'Gölge', 'Turna', 'Bozkurt'];
  const MEKAN = ['Kale', 'Üs', 'Sığınak', 'Meydan', 'Diyar', 'Orman', 'Liman', 'Kamp', 'Karargah', 'Vadi'];
  const asciiFold = (s) => String(s).replace(/ç/g, 'c').replace(/Ç/g, 'C').replace(/ğ/g, 'g').replace(/Ğ/g, 'G').replace(/ı/g, 'i').replace(/İ/g, 'I').replace(/ö/g, 'o').replace(/Ö/g, 'O').replace(/ş/g, 's').replace(/Ş/g, 'S').replace(/ü/g, 'u').replace(/Ü/g, 'U');
  function takmaad(_, ctx) {
    const tur = norm(seg(ctx, 0) || ctx.q('tur')).replace(/[^a-z]/g, '') || 'oyuncu';
    if (!['oyuncu', 'klan', 'sunucu'].includes(tur)) throw fail(400, 'tur: oyuncu, klan veya sunucu');
    const adet = clamp(int(ctx.q('adet'), 5), 1, 20), names = [];
    for (let i = 0; i < adet; i++) {
      names.push(tur === 'oyuncu' ? (wantsTrue(ctx.q('turkce')) ? `${pick(SIFAT)}${pick(ISIM)}${randomInt(1, 100)}` : asciiFold(`${pick(SIFAT)}${pick(ISIM)}${randomInt(1, 100)}`))
        : tur === 'klan' ? `${pick(ISIM)} ${pick(['Birliği', 'Kardeşliği', 'Ordusu', 'Loncası', 'Klanı'])}` : `${pick(SIFAT)} ${pick(MEKAN)}`);
    }
    return { tur, isimler: names };
  }

  // ---- 31. /karakter ----
  const IRKLAR = ['İnsan', 'Elf', 'Cüce', 'Ork', 'Cin', 'Yarı-ejder', 'Cüce-elf melezi', 'Gölge soylu'];
  const SINIFLAR = ['Savaşçı', 'Büyücü', 'Okçu', 'Hırsız', 'Şifacı', 'Paladin', 'Druid', 'Ozan', 'Keşiş', 'Avcı'];
  const SILAHLAR = ['Uzun kılıç', 'Savaş baltası', 'Asa', 'Yay', 'Hançer', 'Çekiç', 'Mızrak', 'Kısa kılıç', 'Büyü kitabı'];
  const KISILIK = ['Cesur', 'Alaycı', 'Meraklı', 'Sakin', 'Hırslı', 'Cömert', 'Huysuz', 'Neşeli', 'Gizemli', 'Sadık'];
  const GECMIS = ['Eski bir kalenin muhafızıydı.', 'Küçük bir köyde şifacının yanında büyüdü.', 'Kayıp bir hazinenin peşinde.', 'Eski ustasını arıyor.', 'Bir akademiden kovuldu.', 'Yıllarca denizlerde dolaştı.', 'Yolculardan topladığı hikayelerle yaşıyor.'];
  const ISIM_A = ['Ar', 'Bel', 'Kor', 'Tha', 'El', 'Gor', 'Mir', 'Ze', 'Lu', 'Ka'], ISIM_B = ['dan', 'ria', 'gath', 'wen', 'mir', 'dis', 'lan', 'ros', 'thor', 'nor'];
  function karakter(_, ctx) {
    const roll = () => { const d = [1, 2, 3, 4].map(() => randomInt(1, 7)); return d.reduce((a, b) => a + b, 0) - Math.min(...d); };
    return { isim: `${pick(ISIM_A)}${pick(ISIM_B)}`, irk: pick(IRKLAR), sinif: pick(SINIFLAR), kisilik: pick(KISILIK), silah: pick(SILAHLAR), seviye: 1, guc: roll(), ceviklik: roll(), dayaniklilik: roll(), zeka: roll(), bilgelik: roll(), karizma: roll(), gecmis: pick(GECMIS), not: 'Özellikler 4 zar atıp en küçüğünü atma yöntemiyle üretilir.' };
  }

  // ---- 32. /hediye ----
  const HEDIYE = {
    anne: { uygun: ['Güzel bir el kremi seti', 'Fotoğraf çerçevesi ve aile fotoğrafı'], orta: ['Kaliteli bir çay veya kahve seti', 'Şık bir şal ya da eşarp'], ozel: ['Spa veya masaj günü', 'Kişiye özel takı'] },
    baba: { uygun: ['İyi bir kahve veya çay seti', 'Kullanışlı bir cüzdan'], orta: ['Kaliteli bir kol saati', 'Şık bir kemer ve kravat'], ozel: ['Balık tutma veya hobi ekipmanı', 'Hafta sonu kaçamağı'] },
    sevgili: { uygun: ['El yazısıyla mektup ve çiçek', 'Birlikte çekilmiş fotoğraflardan albüm'], orta: ['Güzel bir restoranda akşam yemeği', 'Parfüm veya kolonya'], ozel: ['Kısa bir tatil', 'Kişiye özel takı veya saat'] },
    arkadas: { uygun: ['Kitap ve el yapımı kart', 'Eğlenceli bir kupa'], orta: ['Kutu oyunu', 'Kulaklık veya telefon aksesuarı'], ozel: ['Konser veya etkinlik bileti', 'Birlikte bir deneyim günü'] },
    cocuk: { uygun: ['Boyama seti', 'Hikaye kitabı'], orta: ['Yapboz veya zeka oyunu', 'Bisiklet kaskı veya spor aksesuarı'], ozel: ['Eğitici deney seti', 'Bisiklet veya paten'] },
    ofis: { uygun: ['Kaliteli bir defter ve kalem', 'Masa bitkisi'], orta: ['Termos veya şık bir kupa', 'Çay kahve hediye kutusu'], ozel: ['Kablosuz kulaklık', 'Ergonomik masa aksesuarı'] },
  };
  function hediye(_, ctx) {
    const kisi = norm(seg(ctx, 0) || ctx.q('kisi')).replace(/[^a-z]/g, '');
    if (!kisi) return { kisiler: Object.keys(HEDIYE), butceler: ['uygun', 'orta', 'ozel'], kullanim: '/hediye/anne?butce=orta' };
    if (!HEDIYE[kisi]) throw fail(404, `kisi: ${Object.keys(HEDIYE).join(', ')}`);
    const b = norm(ctx.q('butce')).replace(/[^a-z]/g, '') || pick(['uygun', 'orta', 'ozel']);
    if (!HEDIYE[kisi][b]) throw fail(400, 'butce: uygun, orta veya ozel');
    return { kisi, butce: b, oneriler: HEDIYE[kisi][b], rastgele_oneri: pick(HEDIYE[kisi][b]) };
  }

  // ======================= 3. DALGA: yazılımcı araçları =======================
  // ---- 41. /sahte/kisi ----
  const ERKEK = ['Ahmet', 'Mehmet', 'Mustafa', 'Ali', 'Hasan', 'Hüseyin', 'İbrahim', 'Emre', 'Burak', 'Can', 'Cem', 'Kerem', 'Murat', 'Oğuz', 'Serkan', 'Tolga', 'Volkan', 'Yusuf', 'Barış', 'Eren', 'Kaan', 'Onur', 'Selim', 'Umut', 'Berk', 'Deniz', 'Efe', 'Furkan', 'Gökhan', 'Orhan'];
  const KADIN = ['Ayşe', 'Fatma', 'Zeynep', 'Elif', 'Merve', 'Esra', 'Selin', 'Büşra', 'Derya', 'Ebru', 'Gül', 'Hande', 'İpek', 'Melis', 'Nazlı', 'Özge', 'Pınar', 'Seda', 'Tuğba', 'Yasemin', 'Ceren', 'Damla', 'Eda', 'Gamze', 'Irmak', 'Naz', 'Sevgi', 'Sibel', 'Burcu', 'Duygu'];
  const SOYAD = ['Yılmaz', 'Kaya', 'Demir', 'Şahin', 'Çelik', 'Yıldız', 'Yıldırım', 'Öztürk', 'Aydın', 'Özdemir', 'Arslan', 'Doğan', 'Kılıç', 'Aslan', 'Çetin', 'Kara', 'Koç', 'Kurt', 'Özkan', 'Şimşek', 'Polat', 'Korkmaz', 'Erdoğan', 'Güneş', 'Aksoy', 'Acar', 'Bulut', 'Tekin', 'Avcı', 'Türk'];
  function genTckn() {
    const d = [randomInt(1, 10)];
    for (let i = 1; i < 9; i++) d.push(randomInt(0, 10));
    d.push((((d[0] + d[2] + d[4] + d[6] + d[8]) * 7 - (d[1] + d[3] + d[5] + d[7])) % 10 + 10) % 10);
    d.push(d.reduce((a, b) => a + b, 0) % 10);
    return d.join('');
  }
  function genIban() {
    const bank = pick(['00010', '00012', '00046', '00062', '00064', '00067', '00111']);
    let acc = '';
    for (let i = 0; i < 16; i++) acc += randomInt(0, 10);
    const bban = `${bank}0${acc}`;
    const check = 98n - (BigInt(`${bban}292700`) % 97n);
    return `TR${String(check).padStart(2, '0')}${bban}`;
  }
  function sahte(_, ctx) {
    const sub = norm(seg(ctx, 0) || 'kisi');
    if (sub !== 'kisi') throw fail(404, 'Kullanım: /sahte/kisi?adet=3&cinsiyet=kadin');
    const adet = clamp(int(ctx.q('adet'), 1), 1, 20), cin = norm(ctx.q('cinsiyet') || '');
    if (cin && !['erkek', 'kadin'].includes(cin)) throw fail(400, 'cinsiyet: erkek veya kadin');
    const people = [];
    for (let i = 0; i < adet; i++) {
      const kadin = cin ? cin === 'kadin' : randomInt(0, 2) === 1, ad = pick(kadin ? KADIN : ERKEK), soyad = pick(SOYAD), il = pick(IL), y = randomInt(1950, 2006);
      const slug = `${norm(ad).replace(/\s/g, '')}.${norm(soyad).replace(/\s/g, '')}${randomInt(1, 1000)}`;
      people.push({
        ad, soyad, cinsiyet: kadin ? 'kadin' : 'erkek', tckn: genTckn(), dogum_tarihi: `${y}-${pad(randomInt(1, 13))}-${pad(randomInt(1, 29))}`,
        telefon: `+90 5${randomInt(30, 60)} ${randomInt(100, 1000)} ${pad(randomInt(0, 100))} ${pad(randomInt(0, 100))}`, eposta: `${slug}@example.com`, kullanici_adi: slug,
        iban: genIban(), il: il[1], plaka: pad(il[0]), adres: `${pick(['Atatürk', 'Cumhuriyet', 'Barış', 'Gül', 'Yıldız'])} Mah. ${randomInt(1, 200)}. Sok. No:${randomInt(1, 60)} Daire:${randomInt(1, 20)} / ${il[1]}`,
      });
    }
    return { test_verisi: true, kisiler: people, not: 'Sadece test içindir. TCKN ve IBAN doğrulama algoritmasını geçer ama gerçek kişiye ait değildir. Telefon numaraları tesadüfen gerçek olabilir, gerçek mesaj veya arama için kullanmayın.' };
  }

  // ---- 42. /cron ----
  const CRON_MACRO = { '@yearly': '0 0 1 1 *', '@annually': '0 0 1 1 *', '@monthly': '0 0 1 * *', '@weekly': '0 0 * * 0', '@daily': '0 0 * * *', '@midnight': '0 0 * * *', '@hourly': '0 * * * *' };
  const MON_N = { jan: 1, feb: 2, mar: 3, apr: 4, may: 5, jun: 6, jul: 7, aug: 8, sep: 9, oct: 10, nov: 11, dec: 12 };
  const DOW_N = { sun: 0, mon: 1, tue: 2, wed: 3, thu: 4, fri: 5, sat: 6 };
  function cronField(f, min, max, names, what) {
    const set = new Set();
    for (const part of f.split(',')) {
      const m = part.match(/^(\*|[A-Za-z0-9]+(?:-[A-Za-z0-9]+)?)(?:\/(\d+))?$/);
      if (!m) throw fail(400, `Geçersiz cron alanı (${what}): ${f}`);
      const val = (v) => { if (/^\d+$/.test(v)) return +v; const k = names?.[v.toLowerCase()]; if (k === undefined) throw fail(400, `Geçersiz değer (${what}): ${v}`); return k; };
      let lo, hi;
      if (m[1] === '*') [lo, hi] = [min, max];
      else if (m[1].includes('-')) [lo, hi] = m[1].split('-').map(val);
      else { lo = val(m[1]); hi = m[2] ? max : lo; }
      const step = m[2] ? +m[2] : 1;
      if (!step || lo < min || hi > max || lo > hi) throw fail(400, `Aralık dışı (${what}): ${part}`);
      for (let v = lo; v <= hi; v += step) set.add(v);
    }
    return set;
  }
  function cron(_, ctx) {
    let expr = (ctx.q('ifade') || ctx.q('q') || ctx.rest.map(dec).join(' ') || '').trim().replace(/\s+/g, ' ');
    if (!expr) throw fail(400, 'Kullanım: /cron?ifade=*/15 9-17 * * 1-5 (dakika saat gün ay haftanın_günü)');
    if (expr.length > 100) throw fail(400, 'İfade çok uzun');
    const orig = expr;
    if (CRON_MACRO[expr.toLowerCase()]) expr = CRON_MACRO[expr.toLowerCase()];
    const f = expr.split(' ');
    if (f.length !== 5) throw fail(400, 'Cron ifadesi 5 alan içermeli: dakika saat gün ay haftanın_günü');
    const mi = cronField(f[0], 0, 59, null, 'dakika'), hr = cronField(f[1], 0, 23, null, 'saat'), dom = cronField(f[2], 1, 31, null, 'ayın günü'), mo = cronField(f[3], 1, 12, MON_N, 'ay');
    const dowRaw = cronField(f[4], 0, 7, DOW_N, 'haftanın günü'), dow = new Set([...dowRaw].map((d) => d % 7));
    const domAny = f[2] === '*', dowAny = f[4] === '*';
    const list = (set, fmt = (x) => x) => [...set].sort((a, b) => a - b).map(fmt).join(', ');
    const span = (set) => { const a = [...set].sort((x, y) => x - y); return a.length > 2 && a[a.length - 1] - a[0] + 1 === a.length ? `${a[0]}-${a[a.length - 1]} arası` : null; };
    const desc = (s, field, unit) => (field === '*' ? `her ${unit}` : /^\*\/\d+$/.test(field) ? `her ${field.slice(2)} ${unit}${unit === 'dakika' ? 'da' : 'te'} bir` : span(s) ? `${span(s)} (${unit})` : `${list(s)}. ${unit}`);
    const ozet = [];
    if (f[0] !== '*' && f[1] !== '*' && mi.size === 1 && hr.size === 1) ozet.push(`${pad([...hr][0])}:${pad([...mi][0])}'de`);
    else { ozet.push(f[0] === '*' ? 'her dakika' : /^\*\/\d+$/.test(f[0]) ? `her ${f[0].slice(2)} dakikada bir` : `dakika ${list(mi)}`); if (f[1] !== '*') ozet.push(span(hr) ? `saat ${span(hr)}` : hr.size > 1 ? `saat ${list(hr)}` : `saat ${list(hr)}'te`); }
    const parts = [];
    if (!domAny) parts.push(`ayın ${list(dom)}. günü`);
    if (f[3] !== '*') parts.push(`aylar: ${list(mo, (x) => MONTHS[x - 1])}`);
    if (!dowAny) parts.push(`günler: ${list(dow, (x) => DAYS[x])}`);
    const base = Date.now() + 3 * 36e5, start = Math.floor(base / 864e5) * 864e5, out = [], N = clamp(int(ctx.q('adet'), 5), 1, 10);
    for (let d = 0; d < 800 && out.length < N; d++) {
      const day = new Date(start + d * 864e5);
      if (!mo.has(day.getUTCMonth() + 1)) continue;
      const okDom = dom.has(day.getUTCDate()), okDow = dow.has(day.getUTCDay());
      if (!(domAny && dowAny ? true : domAny ? okDow : dowAny ? okDom : okDom || okDow)) continue;
      for (const h of [...hr].sort((a, b) => a - b)) for (const m of [...mi].sort((a, b) => a - b)) {
        const t = start + d * 864e5 + (h * 60 + m) * 60e3;
        if (t > base && out.length < N) out.push(new Date(t).toISOString().slice(0, 16).replace('T', ' '));
      }
    }
    return {
      ifade: orig, dakika: desc(mi, f[0], 'dakika'), saat: desc(hr, f[1], 'saat'), ayin_gunu: domAny ? 'her gün' : list(dom), ay: f[3] === '*' ? 'her ay' : list(mo, (x) => MONTHS[x - 1]), haftanin_gunu: dowAny ? 'her gün' : list(dow, (x) => DAYS[x]),
      ozet: [ozet.join(' '), ...parts].join(', '), sonraki_calisma_tr_saati: out, not: 'Sonraki çalışma zamanları Türkiye saatiyle (UTC+3) verilir. Hem ayın günü hem haftanın günü verilirse standart cron gibi VEYA mantığı uygulanır.',
    };
  }

  // ---- 43. /durumkodu ----
  const HTTP = {
    100: ['Continue', 'Devam', 'İstemci isteğe devam edebilir.'], 101: ['Switching Protocols', 'Protokol değiştiriliyor', 'Sunucu, protokol değiştirme isteğini kabul etti (örn. WebSocket).'],
    200: ['OK', 'Başarılı', 'İstek başarıyla işlendi.'], 201: ['Created', 'Oluşturuldu', 'Yeni kaynak başarıyla oluşturuldu.'], 202: ['Accepted', 'Kabul edildi', 'İstek alındı ama işlem henüz bitmedi.'], 204: ['No Content', 'İçerik yok', 'İşlem başarılı, dönecek içerik yok.'], 206: ['Partial Content', 'Kısmi içerik', 'İçeriğin yalnızca istenen kısmı döndü.'],
    301: ['Moved Permanently', 'Kalıcı yönlendirme', 'Kaynak kalıcı olarak yeni adrese taşındı.'], 302: ['Found', 'Geçici yönlendirme', 'Kaynak geçici olarak başka adreste.'], 303: ['See Other', 'Başka yere bak', 'Sonuç için başka bir adrese GET isteği yapılmalı.'], 304: ['Not Modified', 'Değişmedi', 'İçerik değişmedi, önbellekteki kullanılabilir.'], 307: ['Temporary Redirect', 'Geçici yönlendirme (yöntem korunur)', 'İstek aynı yöntemle başka adrese yapılmalı.'], 308: ['Permanent Redirect', 'Kalıcı yönlendirme (yöntem korunur)', 'Kalıcı olarak taşındı, aynı yöntem kullanılmalı.'],
    400: ['Bad Request', 'Hatalı istek', 'İstek sunucu tarafından anlaşılamadı veya geçersiz.'], 401: ['Unauthorized', 'Yetkisiz', 'Kimlik doğrulaması gerekli veya başarısız.'], 403: ['Forbidden', 'Yasak', 'Kimliğiniz var ama bu kaynağa erişim izniniz yok.'], 404: ['Not Found', 'Bulunamadı', 'İstenen kaynak bulunamadı.'], 405: ['Method Not Allowed', 'Yönteme izin yok', 'Bu adreste bu HTTP yöntemi desteklenmiyor.'],
    406: ['Not Acceptable', 'Kabul edilemez', 'Sunucu, istenen içerik türünü üretemiyor.'], 408: ['Request Timeout', 'İstek zaman aşımı', 'İstemci isteği zamanında göndermedi.'], 409: ['Conflict', 'Çakışma', 'İstek, kaynağın mevcut durumuyla çakışıyor.'], 410: ['Gone', 'Kalıcı olarak yok', 'Kaynak kalıcı olarak kaldırıldı.'],
    413: ['Payload Too Large', 'İçerik çok büyük', 'Gönderilen veri sunucunun sınırını aşıyor.'], 414: ['URI Too Long', 'Adres çok uzun', 'İstek adresi çok uzun.'], 415: ['Unsupported Media Type', 'Desteklenmeyen medya türü', 'Gönderilen içerik türü desteklenmiyor.'], 418: ['I\'m a teapot', 'Ben bir demlikim', 'Şaka amaçlı bir koddur (RFC 2324).'],
    422: ['Unprocessable Content', 'İşlenemeyen içerik', 'Biçim doğru ama içerik anlamsal olarak geçersiz.'], 429: ['Too Many Requests', 'Çok fazla istek', 'Hız sınırı aşıldı, daha sonra tekrar deneyin.'], 431: ['Request Header Fields Too Large', 'Başlıklar çok büyük', 'İstek başlıkları çok büyük.'], 451: ['Unavailable For Legal Reasons', 'Hukuki nedenlerle erişilemez', 'Yasal nedenle içeriğe erişim engellenmiş.'],
    500: ['Internal Server Error', 'Sunucu hatası', 'Sunucuda beklenmeyen bir hata oluştu.'], 501: ['Not Implemented', 'Uygulanmadı', 'Sunucu bu isteği destekleyecek yetenekte değil.'], 502: ['Bad Gateway', 'Hatalı ağ geçidi', 'Ağ geçidi, üst sunucudan geçersiz yanıt aldı.'], 503: ['Service Unavailable', 'Hizmet kullanılamıyor', 'Sunucu geçici olarak hizmet veremiyor (bakım veya aşırı yük).'], 504: ['Gateway Timeout', 'Ağ geçidi zaman aşımı', 'Ağ geçidi, üst sunucudan zamanında yanıt alamadı.'], 505: ['HTTP Version Not Supported', 'HTTP sürümü desteklenmiyor', 'Kullanılan HTTP sürümü desteklenmiyor.'],
  };
  const httpClass = (c) => ({ 1: 'Bilgi', 2: 'Başarılı', 3: 'Yönlendirme', 4: 'İstemci hatası', 5: 'Sunucu hatası' }[Math.floor(c / 100)]);
  function durumkodu(_, ctx) {
    const raw = seg(ctx, 0) || ctx.q('kod');
    if (!raw) return { kodlar: Object.entries(HTTP).map(([k, v]) => `${k} ${v[1]}`), kullanim: '/durumkodu/404' };
    if (!/^\d{3}$/.test(raw)) throw fail(400, 'Kod 3 haneli olmalı (örn. 404)');
    const e = HTTP[+raw];
    if (!e) return { kod: +raw, kategori: httpClass(+raw) || 'Bilinmiyor', bilinen_kod: false, aciklama: 'Bu kod yaygın olarak tanımlı değil.' };
    return { kod: +raw, kategori: httpClass(+raw), ingilizce: e[0], turkce: e[1], aciklama: e[2] };
  }

  // ---- 44. /cidr ----
  const ip2int = (ip) => { const p = ip.split('.'); if (p.length !== 4 || p.some((x) => !/^\d{1,3}$/.test(x) || +x > 255)) throw fail(400, 'Geçersiz IPv4 adresi'); return ((+p[0] << 24) >>> 0) + (+p[1] << 16) + (+p[2] << 8) + +p[3]; };
  const int2ip = (n) => [n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255].join('.');
  function cidr(_, ctx) {
    const raw = (ctx.rest.length ? ctx.rest.map(dec).join('/') : ctx.q('ag') || ctx.q('q') || '').trim();
    if (!raw) throw fail(400, 'Kullanım: /cidr/192.168.1.0/24');
    if (raw.includes(':')) throw fail(400, 'Şimdilik sadece IPv4 destekleniyor');
    const [ipS, pS = '32'] = raw.split('/');
    if (!/^\d{1,2}$/.test(pS) || +pS > 32) throw fail(400, 'Önek uzunluğu 0-32 arasında olmalı');
    const p = +pS, ip = ip2int(ipS), mask = p === 0 ? 0 : (0xffffffff << (32 - p)) >>> 0, net = (ip & mask) >>> 0, bc = (net | (~mask >>> 0)) >>> 0, total = 2 ** (32 - p);
    const hosts = p <= 30 ? total - 2 : p === 31 ? 2 : 1, first = p <= 30 ? net + 1 : net, last = p <= 30 ? bc - 1 : bc, o1 = ip >>> 24;
    const inR = (a, b, bits) => { const m = bits === 0 ? 0 : (0xffffffff << (32 - bits)) >>> 0; return (ip & m) >>> 0 === ip2int(a) >>> 0; };
    const ozel = inR('10.0.0.0', 0, 8) ? 'Özel ağ (10.0.0.0/8)' : inR('172.16.0.0', 0, 12) ? 'Özel ağ (172.16.0.0/12)' : inR('192.168.0.0', 0, 16) ? 'Özel ağ (192.168.0.0/16)' : inR('127.0.0.0', 0, 8) ? 'Loopback' : inR('169.254.0.0', 0, 16) ? 'Link-local' : inR('100.64.0.0', 0, 10) ? 'CGNAT' : null;
    return { girilen: `${ipS}/${p}`, ag_adresi: int2ip(net), alt_ag_maskesi: int2ip(mask), wildcard_maskesi: int2ip(~mask >>> 0), yayin_adresi: int2ip(bc), ilk_kullanilabilir: int2ip(first), son_kullanilabilir: int2ip(last), toplam_adres: total, kullanilabilir_host: hosts, ip_sinifi: o1 < 128 ? 'A' : o1 < 192 ? 'B' : o1 < 224 ? 'C' : o1 < 240 ? 'D (multicast)' : 'E (ayrılmış)', ozel_adres: ozel };
  }

  // ---- 45. /ua ----
  function ua(_, ctx) {
    const s = (ctx.q('q') || ctx.q('ua') || ctx.req?.headers?.['user-agent'] || '').slice(0, 500);
    if (!s) throw fail(400, 'Kullanım: /ua?q={user-agent}. Boş bırakırsanız isteği yapan tarayıcı çözülür.');
    const m = (re) => s.match(re);
    let tarayici = 'Bilinmiyor', surum = null, motor = null;
    const T = [[/SamsungBrowser\/([\d.]+)/, 'Samsung Internet'], [/(?:Edg|EdgA|EdgiOS)\/([\d.]+)/, 'Edge'], [/OPR\/([\d.]+)/, 'Opera'], [/(?:Firefox|FxiOS)\/([\d.]+)/, 'Firefox'], [/(?:Chrome|CriOS)\/([\d.]+)/, 'Chrome'], [/Version\/([\d.]+).*Safari/, 'Safari'], [/curl\/([\d.]+)/, 'curl'], [/Postman/, 'Postman']];
    for (const [re, n] of T) { const r = m(re); if (r) { tarayici = n; surum = r[1] || null; break; } }
    motor = /Firefox|FxiOS/.test(s) ? 'Gecko' : /AppleWebKit/.test(s) ? (/Chrome|CriOS|Edg|OPR/.test(s) ? 'Blink' : 'WebKit') : null;
    let os = 'Bilinmiyor', osSurum = null, r;
    if ((r = m(/Windows NT ([\d.]+)/))) { os = 'Windows'; osSurum = { '10.0': '10 / 11', '6.3': '8.1', '6.2': '8', '6.1': '7' }[r[1]] || r[1]; }
    else if ((r = m(/(?:iPhone|CPU) OS ([\d_]+)/)) && /iPhone|iPad/.test(s)) { os = /iPad/.test(s) ? 'iPadOS' : 'iOS'; osSurum = r[1].replace(/_/g, '.'); }
    else if ((r = m(/Android ([\d.]+)/))) { os = 'Android'; osSurum = r[1]; }
    else if ((r = m(/Mac OS X ([\d_]+)/))) { os = 'macOS'; osSurum = r[1].replace(/_/g, '.'); }
    else if (/CrOS/.test(s)) os = 'ChromeOS';
    else if (/Linux/.test(s)) os = 'Linux';
    const bot = /bot|crawl|spider|slurp|curl|wget|python-requests|httpclient|axios|postman|discord|telegram|facebookexternalhit/i.test(s);
    const cihaz = bot ? 'Bot / araç' : /iPad|Tablet|Android(?!.*Mobile)/i.test(s) ? 'Tablet' : /Mobile|iPhone|Android/i.test(s) ? 'Mobil' : 'Masaüstü';
    return { tarayici, tarayici_surumu: surum, motor, isletim_sistemi: os, isletim_sistemi_surumu: osSurum, cihaz_turu: cihaz, bot_mu: bot, user_agent: s };
  }

  // ---- 46. /lorem ----
  const LOREM = ['güneş', 'deniz', 'yolculuk', 'sabah', 'masal', 'rüzgar', 'dağ', 'orman', 'hikaye', 'sessizlik', 'umut', 'şehir', 'bahar', 'zaman', 'ışık', 'gölge', 'kitap', 'pencere', 'bulut', 'çiçek', 'nehir', 'köprü', 'melodi', 'sokak', 'akşam', 'yıldız', 'dalga', 'hayal', 'bahçe', 'kuş', 've', 'ile', 'gibi', 'sonra', 'yavaşça', 'derin', 'sessizce', 'yeni', 'eski', 'uzak', 'sıcak', 'serin', 'güzel', 'parlak', 'huzurlu', 'gizemli', 'sabırla', 'bekler', 'akar', 'yürür', 'düşünür', 'gülümser', 'anlatır', 'saklar', 'bulur', 'taşır', 'çağırır', 'değişir', 'büyür'];
  function lorem(_, ctx) {
    const p = clamp(int(seg(ctx, 0) || ctx.q('paragraf'), 3), 1, 10), c = clamp(int(ctx.q('cumle'), 4), 1, 10);
    const sentence = () => { const n = randomInt(6, 13), w = Array.from({ length: n }, () => pick(LOREM)); return `${trUpper(w[0][0])}${w[0].slice(1)} ${w.slice(1).join(' ')}.`; };
    return { paragraf_sayisi: p, paragraflar: Array.from({ length: p }, () => Array.from({ length: c }, sentence).join(' ')) };
  }

  // ---- 47. /json ----
  function jsonTool(_, ctx) {
    const raw = ctx.q('q') || ctx.q('json') || ctx.rest.map(dec).join('/');
    if (!raw) throw fail(400, 'Kullanım: /json?q={"a":1}&islem=format|minify|dogrula');
    if (raw.length > 5000) throw fail(400, 'En fazla 5000 karakter');
    const islem = norm(ctx.q('islem') || 'format');
    if (!['format', 'minify', 'dogrula'].includes(islem)) throw fail(400, 'islem: format, minify veya dogrula');
    let v;
    try { v = JSON.parse(raw); } catch (e) { return { gecerli: false, hata: String(e.message).slice(0, 200), not: 'Metin geçerli bir JSON değil.' }; }
    const tur = Array.isArray(v) ? 'dizi' : v === null ? 'null' : typeof v === 'object' ? 'nesne' : typeof v;
    const out = { gecerli: true, tur, ...(tur === 'nesne' ? { anahtar_sayisi: Object.keys(v).length } : tur === 'dizi' ? { eleman_sayisi: v.length } : {}) };
    if (islem === 'format') out.sonuc = JSON.stringify(v, null, 2).split('\n');
    if (islem === 'minify') out.sonuc = JSON.stringify(v);
    return out;
  }

  // ---- 48. /regex ----
  function regexTool(_, ctx) {
    const desen = ctx.q('desen') || ctx.q('regex'), metin = ctx.q('metin') || ctx.q('text') || '';
    if (!desen) throw fail(400, 'Kullanım: /regex?desen=\\d+&metin=abc123&bayrak=gi');
    if (desen.length > 100 || metin.length > 1000) throw fail(400, 'Desen en fazla 100, metin en fazla 1000 karakter olabilir');
    const flags = (ctx.q('bayrak') || '').replace(/[^gimsuy]/g, '');
    if (new Set(flags).size !== flags.length) throw fail(400, 'Bayraklar tekrar edemez');
    if (/(\+|\*|\{\d*,?\d*\})\)?(\+|\*|\{)/.test(desen)) throw fail(400, 'İç içe tekrar eden nicelleyiciler güvenlik nedeniyle desteklenmiyor');
    let re;
    try { re = new RegExp(desen, flags.includes('g') ? flags : flags + 'g'); } catch (e) { return { gecerli: false, hata: String(e.message).slice(0, 200) }; }
    let found;
    try {
      found = require('vm').runInNewContext('var out=[],m,n=0;while((m=re.exec(text))!==null&&n<50){out.push({m:m[0],i:m.index,g:m.slice(1)});n++;if(m[0]==="")re.lastIndex++;}out', { re, text: metin }, { timeout: 150 });
    } catch { throw fail(400, 'Desen çalıştırılamadı veya çok uzun sürdü'); }
    return { gecerli: true, desen, bayrak: flags || null, eslesme_sayisi: found.length, eslesmeler: found.map((x) => ({ metin: x.m, indeks: x.i, gruplar: x.g.map((g) => g ?? null) })) };
  }

  // ---- 49. /metinstil ----
  const MORSE = { a: '.-', b: '-...', c: '-.-.', d: '-..', e: '.', f: '..-.', g: '--.', h: '....', i: '..', j: '.---', k: '-.-', l: '.-..', m: '--', n: '-.', o: '---', p: '.--.', q: '--.-', r: '.-.', s: '...', t: '-', u: '..-', v: '...-', w: '.--', x: '-..-', y: '-.--', z: '--..', 0: '-----', 1: '.----', 2: '..---', 3: '...--', 4: '....-', 5: '.....', 6: '-....', 7: '--...', 8: '---..', 9: '----.', '.': '.-.-.-', ',': '--..--', '?': '..--..', '!': '-.-.--' };
  const STYLES = { ters: 'Metni tersten yazar', alternatif: 'aLtErNaTiF büyük/küçük harf', buyuk: 'Türkçe büyük harf (i ve ı doğru)', kucuk: 'Türkçe küçük harf', baslik: 'Her Kelimenin İlk Harfi Büyük', ascii: 'Türkçe karakterleri ASCII yapar', slug: 'URL dostu bağlantı metni', mors: 'Mors alfabesi', binary: 'İkili (binary) kod', hex: 'Onaltılık (hex) kod', leet: 'Leet (1337) yazım', say: 'Kelime, karakter ve cümle sayısı', temizle: 'Fazla boşlukları temizler' };
  function metinstil(_, ctx) {
    const stil = norm(seg(ctx, 0) || ctx.q('stil')).replace(/[^a-z]/g, '');
    if (!stil) return { stiller: Object.entries(STYLES).map(([k, v]) => `${k}: ${v}`), kullanim: '/metinstil/ters?q=Merhaba dünya' };
    if (!STYLES[stil]) throw fail(404, `Stil bulunamadı: ${Object.keys(STYLES).join(', ')}`);
    const q = ctx.q('q') || ctx.rest.slice(1).map(dec).join('/');
    if (!q) throw fail(400, 'q (metin) gerekli');
    if (q.length > 2000) throw fail(400, 'Metin en fazla 2000 karakter olabilir');
    let r;
    const chars = Array.from(q);
    switch (stil) {
      case 'ters': r = chars.reverse().join(''); break;
      case 'alternatif': r = chars.map((c, i) => (i % 2 ? trLower(c) : trUpper(c))).join(''); break;
      case 'buyuk': r = trUpper(q); break;
      case 'kucuk': r = trLower(q); break;
      case 'baslik': r = q.split(' ').map((w) => (w ? trUpper(Array.from(w)[0]) + trLower(Array.from(w).slice(1).join('')) : w)).join(' '); break;
      case 'ascii': r = asciiFold(q); break;
      case 'slug': r = norm(q).replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, ''); break;
      case 'mors': r = [...norm(q)].map((c) => (c === ' ' ? '/' : MORSE[c] || '')).filter((x) => x !== '').join(' '); break;
      case 'binary': if (q.length > 500) throw fail(400, 'Bu stil için en fazla 500 karakter'); r = [...Buffer.from(q, 'utf8')].map((b) => b.toString(2).padStart(8, '0')).join(' '); break;
      case 'hex': r = [...Buffer.from(q, 'utf8')].map((b) => b.toString(16).padStart(2, '0')).join(' '); break;
      case 'leet': r = [...asciiFold(q).toLowerCase()].map((c) => ({ a: '4', e: '3', i: '1', o: '0', s: '5', t: '7' }[c] || c)).join(''); break;
      case 'temizle': r = q.replace(/\s+/g, ' ').trim(); break;
      case 'say': {
        const words = q.trim().split(/\s+/).filter(Boolean);
        return { kelime: words.length, karakter: chars.length, karakter_bosluksuz: chars.filter((c) => !/\s/.test(c)).length, cumle: (q.match(/[.!?]+(\s|$)/g) || []).length || (q.trim() ? 1 : 0) };
      }
    }
    return { stil, girdi: q, sonuc: r };
  }

  // ---- 50. /epostakontrol ----
  const TEK_KULLANIM = new Set(['mailinator.com', 'guerrillamail.com', 'guerrillamail.net', '10minutemail.com', 'tempmail.com', 'temp-mail.org', 'yopmail.com', 'trashmail.com', 'getnada.com', 'sharklasers.com', 'dispostable.com', 'maildrop.cc', 'throwawaymail.com', 'fakeinbox.com', 'mohmal.com', 'emailondeck.com', 'tempail.com', 'mail.tm', 'mintemail.com', 'spamgourmet.com', 'tempinbox.com', 'burnermail.io', 'moakt.com', 'tmpmail.org', 'mailnesia.com', 'inboxkitten.com', 'mytemp.email', 'trashmail.net', 'dropmail.me', 'emailfake.com']);
  const TYPO = { 'gmial.com': 'gmail.com', 'gamil.com': 'gmail.com', 'gmail.con': 'gmail.com', 'gmai.com': 'gmail.com', 'gmaill.com': 'gmail.com', 'hotnail.com': 'hotmail.com', 'hotmial.com': 'hotmail.com', 'hotmal.com': 'hotmail.com', 'outlok.com': 'outlook.com', 'outloook.com': 'outlook.com', 'yahooo.com': 'yahoo.com', 'yaho.com': 'yahoo.com', 'icloud.con': 'icloud.com', 'yandex.con': 'yandex.com' };
  async function epostakontrol(_, ctx) {
    const raw = (seg(ctx, 0) || ctx.q('adres') || ctx.q('q') || '').trim();
    if (!raw) throw fail(400, 'Kullanım: /epostakontrol/ornek@gmail.com');
    if (raw.length > 254) throw fail(400, 'Adres çok uzun');
    const ok = /^[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)+$/.test(raw) && !raw.includes('..') && !raw.split('@')[0].startsWith('.') && !raw.split('@')[0].endsWith('.') && raw.split('@')[0].length <= 64;
    const out = { adres: raw, bicim_gecerli: ok };
    if (!ok) return { ...out, neden: 'E-posta biçimi geçersiz' };
    const domain = raw.split('@')[1].toLowerCase();
    out.alan_adi = domain;
    out.tek_kullanimlik = TEK_KULLANIM.has(domain);
    if (TYPO[domain]) out.oneri = `${raw.split('@')[0]}@${TYPO[domain]}`;
    try {
      const mx = await Promise.race([require('dns').promises.resolveMx(domain), new Promise((_, rej) => setTimeout(() => rej(new Error('zaman asimi')), 4000))]);
      out.mx_var = mx.length > 0;
      out.mx_kayitlari = mx.sort((a, b) => a.priority - b.priority).slice(0, 3).map((x) => x.exchange);
    } catch (e) { out.mx_var = false; out.mx_notu = e.code === 'ENODATA' || e.code === 'ENOTFOUND' ? 'Alan adının posta (MX) kaydı yok' : 'MX sorgusu yapılamadı'; }
    out.teslim_edilebilir_olabilir = out.bicim_gecerli && out.mx_var && !out.tek_kullanimlik;
    out.not = 'Posta kutusunun gerçekten var olup olmadığı doğrulanamaz; sadece biçim, MX kaydı ve tek kullanımlık alan adı kontrol edilir.';
    return out;
  }

  return { hava, havaKalitesi, gunes, ay, doviz, kdv, deprem, wiki, bugun, plaka, burc, yas, tarihFark, bmi, birim, kredi, mevduat, indirim, yuzde, bahsis, kripto, saat, mesafe, tatilKalan, hicri, sozluk, cevir, romen, yaziyla, loto, rastgele, sec, atasozu,
    gno, gecmenotu, boya, elektrik, klima, tuketim, tarihyazi, telefon, dilekce, mesaj, hesapla, aktivite, yemek, giyim, varis, zekat, etkilesim, ship, sekiztop, dogrulukcesaret, fal, iltifat, espri, bilmece, quiz, adamasmaca, wordle, tkm, kart, takmaad, karakter, hediye,
    sahte, cron, durumkodu, cidr, ua, lorem, jsonTool, regexTool, metinstil, epostakontrol };
})();

const ROUTES = {
  whois: domainRoute(whois),
  dns: domainRoute(dnsInfo),
  available: domainRoute(availableInfo),
  ssl: domainRoute(sslInfo),
  headers: domainRoute(headersInfo),
  expand: anyRoute(expand, { param: 'url', cache: true }),
  ip: anyRoute(ipInfo, { param: 'ip', cache: true }),
  asn: anyRoute(asnInfo, { param: 'ip', cache: true }),
  blacklist: anyRoute(blacklist, { param: 'ip', cache: true }),
  mail: anyRoute(mailInfo, { param: 'eposta' }),
  iban: anyRoute(ibanInfo, { param: 'iban' }),
  tckn: anyRoute(tcknInfo, { param: 'tckn' }),
  vkn: anyRoute(vknInfo, { param: 'vergi_no' }),
  tatil: anyRoute(tatilInfo, { param: 'yil' }),
  namaz: anyRoute(namaz, { param: 'sehir' }),
  myip: customRoute(myipRoute),
  hash: customRoute(hashRoute),
  base64: customRoute(base64Route),
  url: customRoute(urlRoute),
  jwt: customRoute(jwtRoute),
  uuid: customRoute(uuidRoute),
  password: customRoute(passwordRoute),
  qr: customRoute(qrRoute),
  qrcode: customRoute(qrCustomRoute),
  minecraft: customRoute(minecraftRoute),
  roll: customRoute(rollRoute),
  flip: customRoute(flipRoute),
  screenshot: customRoute(screenshotRoute),
  lyrics: customRoute(lyricsRoute),
  color: customRoute(colorRoute),
  tempmail: customRoute(tempmailRoute),
  hava: customRoute(EVERYDAY.hava),
  havakalitesi: customRoute(EVERYDAY.havaKalitesi),
  gunes: customRoute(EVERYDAY.gunes),
  ay: customRoute(EVERYDAY.ay),
  doviz: customRoute(EVERYDAY.doviz),
  kdv: customRoute(EVERYDAY.kdv),
  deprem: customRoute(EVERYDAY.deprem),
  wiki: customRoute(EVERYDAY.wiki),
  bugun: customRoute(EVERYDAY.bugun),
  plaka: customRoute(EVERYDAY.plaka),
  burc: customRoute(EVERYDAY.burc),
  yas: customRoute(EVERYDAY.yas),
  tarihfark: customRoute(EVERYDAY.tarihFark),
  bmi: customRoute(EVERYDAY.bmi),
  birim: customRoute(EVERYDAY.birim),
  kredi: customRoute(EVERYDAY.kredi),
  mevduat: customRoute(EVERYDAY.mevduat),
  indirim: customRoute(EVERYDAY.indirim),
  yuzde: customRoute(EVERYDAY.yuzde),
  bahsis: customRoute(EVERYDAY.bahsis),
  kripto: customRoute(EVERYDAY.kripto),
  saat: customRoute(EVERYDAY.saat),
  mesafe: customRoute(EVERYDAY.mesafe),
  tatilkalan: customRoute(EVERYDAY.tatilKalan),
  hicri: customRoute(EVERYDAY.hicri),
  sozluk: customRoute(EVERYDAY.sozluk),
  cevir: customRoute(EVERYDAY.cevir),
  romen: customRoute(EVERYDAY.romen),
  yaziyla: customRoute(EVERYDAY.yaziyla),
  loto: customRoute(EVERYDAY.loto),
  rastgele: customRoute(EVERYDAY.rastgele),
  sec: customRoute(EVERYDAY.sec),
  atasozu: customRoute(EVERYDAY.atasozu),
  gno: customRoute(EVERYDAY.gno),
  gecmenotu: customRoute(EVERYDAY.gecmenotu),
  boya: customRoute(EVERYDAY.boya),
  elektrik: customRoute(EVERYDAY.elektrik),
  klima: customRoute(EVERYDAY.klima),
  tuketim: customRoute(EVERYDAY.tuketim),
  tarihyazi: customRoute(EVERYDAY.tarihyazi),
  telefon: customRoute(EVERYDAY.telefon),
  dilekce: customRoute(EVERYDAY.dilekce),
  mesaj: customRoute(EVERYDAY.mesaj),
  hesapla: customRoute(EVERYDAY.hesapla),
  aktivite: customRoute(EVERYDAY.aktivite),
  yemek: customRoute(EVERYDAY.yemek),
  giyim: customRoute(EVERYDAY.giyim),
  varis: customRoute(EVERYDAY.varis),
  zekat: customRoute(EVERYDAY.zekat),
  etkilesim: customRoute(EVERYDAY.etkilesim),
  ship: customRoute(EVERYDAY.ship),
  '8top': customRoute(EVERYDAY.sekiztop),
  'dogruluk-cesaret': customRoute(EVERYDAY.dogrulukcesaret),
  fal: customRoute(EVERYDAY.fal),
  iltifat: customRoute(EVERYDAY.iltifat),
  espri: customRoute(EVERYDAY.espri),
  bilmece: customRoute(EVERYDAY.bilmece),
  quiz: customRoute(EVERYDAY.quiz),
  adamasmaca: customRoute(EVERYDAY.adamasmaca),
  wordle: customRoute(EVERYDAY.wordle),
  tkm: customRoute(EVERYDAY.tkm),
  kart: customRoute(EVERYDAY.kart),
  takmaad: customRoute(EVERYDAY.takmaad),
  karakter: customRoute(EVERYDAY.karakter),
  hediye: customRoute(EVERYDAY.hediye),
  sahte: customRoute(EVERYDAY.sahte),
  cron: customRoute(EVERYDAY.cron),
  durumkodu: customRoute(EVERYDAY.durumkodu),
  cidr: customRoute(EVERYDAY.cidr),
  ua: customRoute(EVERYDAY.ua),
  lorem: customRoute(EVERYDAY.lorem),
  json: customRoute(EVERYDAY.jsonTool),
  regex: customRoute(EVERYDAY.regexTool),
  metinstil: customRoute(EVERYDAY.metinstil),
  epostakontrol: customRoute(EVERYDAY.epostakontrol),
};

const DOCS = {
  name: 'Domain, IP ve Araçlar API',
  alan_adi_ve_ag: {
    '/whois/{domain}': 'Alan adı kayıt bilgisi (registrar, tarihler, nameserver)',
    '/dns/{domain}': 'DNS kayıtları (A, AAAA, MX, NS, TXT, SPF, DMARC, CAA, SOA)',
    '/available/{domain}': 'Alan adı müsait mi?',
    '/ssl/{domain}': 'SSL sertifikası (bitiş tarihi, veren, geçerlilik, SAN)',
    '/headers/{domain}': 'HTTP header, yönlendirme zinciri, güvenlik header skoru',
    '/expand/{url}': 'Kısa linki açar, yönlendirme zincirini gösterir',
    '/ip/{ip}': 'IP bilgisi (ağ, ülke, organizasyon, ters DNS). Alan adı da verilebilir',
    '/asn/{ip}': 'ASN numarası, ağ bloğu, şirket',
    '/blacklist/{ip}': 'Spam kara liste (DNSBL) kontrolü',
    '/myip': 'Senin IP adresin ve tarayıcı bilgin',
  },
  dogrulama: {
    '/mail/{eposta}': 'E-posta kontrolü (biçim, MX, tek kullanımlık, yazım hatası)',
    '/iban/{iban}': 'IBAN doğrulama, TR için banka',
    '/tckn/{no}': 'TC kimlik no algoritma doğrulaması',
    '/vkn/{no}': 'Vergi kimlik no algoritma doğrulaması',
  },
  turkiye: {
    '/tatil/{yil}': 'Resmi tatiller ve iş günü sayısı (örn. /tatil/2026)',
    '/tatil/{yyyy-aa-gg}': 'O gün tatil mi, iş günü mü, sonraki iş günü (örn. /tatil/2026-10-29)',
    '/namaz/{sehir}': 'Diyanet namaz vakitleri, sıradaki vakit (?ulke=Germany ile başka ülke)',
  },
  araclar: {
    '/hash/{metin}': 'md5, sha1, sha256, sha384, sha512 (tek algoritma: /hash/sha256/{metin}, HMAC: ?key=...)',
    '/base64/encode/{metin}': 'Base64 kodla',
    '/base64/decode/{base64}': 'Base64 çöz',
    '/url/encode/{metin}': 'URL kodla',
    '/url/decode/{metin}': 'URL çöz',
    '/jwt/{token}': 'JWT içeriğini çözer (imza doğrulamaz)',
    '/uuid': 'UUID üretir (?adet=5, ?v=7)',
    '/password': 'Güvenli parola üretir (?uzunluk=20&adet=3&ozel=0&rakam=0&buyuk=0)',
    '/qr/{metin}': 'QR kod görseli (?format=png|svg|text, ?ecc=L|M|Q|H, ?scale=8, ?margin=4)',
    '/qrcode/custom?text={metin}&logo={https-url}': 'Ortada logo veya simge olan SVG QR kodu',
    '/color/{hex}': 'HEX rengini JSON olarak veya ?format=svg ile görsel olarak döndürür',
    '/roll/{NdM}': 'Zar atar (örn. /roll/2d6)',
    '/flip?count={adet}': 'Yazı-tura atar',
    '/minecraft/{sunucu[:port]}': 'Minecraft sunucu durumu, oyuncu sayısı ve MOTD',
    '/screenshot?url={https-url}': 'Bir web sayfasının ekran görüntüsünü PNG/JPEG olarak döndürür',
    '/lyrics?q={şarkı}': 'LRCLIB kataloğunda şarkı sözü arar',
    'POST /tempmail/new': 'Geçici e-posta adresi açar; oturum bellekte tutulur',
    '/tempmail/inbox/{id}': 'Geçici e-posta gelen kutusunu kontrol eder',
  },
  gunluk_hayat: {
    '/hava/{sehir}': 'Anlık hava durumu ve 5 günlük tahmin (?ulke=DE ile ülke seç)',
    '/havakalitesi/{sehir}': 'Hava kalitesi indeksi (AQI), PM2.5, PM10, ozon',
    '/gunes/{sehir}': 'Gün doğumu, gün batımı, gün uzunluğu, UV indeksi',
    '/ay': 'Ay evresi, aydınlanma yüzdesi, sonraki dolunay (?tarih=2026-10-29)',
    '/doviz': 'TCMB gösterge kurlarının tamamı',
    '/doviz/{kod}': 'Tek bir kurun TL karşılığı (örn. /doviz/usd)',
    '/doviz/{kod}/{hedef}?miktar=100': 'Para birimi çevirici (örn. /doviz/usd/try?miktar=100)',
    '/kdv/{tutar}': 'KDV hesaplama (?oran=20, ?dahil=1 tutar KDV dahilse)',
    '/deprem': 'Son 72 saatteki depremler (?min=3&limit=10&il=izmir)',
    '/wiki/{konu}': 'Vikipedi madde özeti (?dil=en ile başka dil)',
    '/bugun': 'Tarihte bugün (?tarih=10-29&tur=events|births|deaths|holidays&limit=10)',
    '/plaka/{kod}': 'Plaka kodundan il, ilden plaka, alan koduyla il (örn. /plaka/34, /plaka/izmir, /plaka/312)',
    '/burc/{tarih}': 'Doğum tarihinden burç (yyyy-aa-gg veya aa-gg)',
  },
  para_ve_finans: {
    '/kripto': 'Popüler kripto paralar (TL ve USD)',
    '/kripto/{coin}': 'Tek coin fiyatı (örn. /kripto/btc)',
    '/kredi/{tutar}/{vade}?faiz=3.5': 'Kredi taksit hesaplama (?tur=yillik ile yıllık faiz)',
    '/mevduat/{anapara}/{gun}?faiz=45': 'Mevduat getiri hesaplama (?stopaj=15)',
    '/indirim/{fiyat}/{oran}': 'İndirimli fiyat hesaplama',
    '/yuzde/{a}/{b}': 'Yüzde hesaplama (yüzdesi, artış, azalış, değişim)',
    '/bahsis/{hesap}?yuzde=10&kisi=4': 'Bahşiş ve hesap bölüşme',
  },
  gunluk_araclar: {
    '/saat/{sehir}': 'Şehrin yerel saati (veya /saat/Europe/London)',
    '/mesafe/{sehir1}/{sehir2}': 'İki şehir arası kuş uçuşu mesafe',
    '/tatilkalan': 'Sonraki resmi tatile kaç gün kaldı',
    '/hicri/{tarih}': 'Hicri takvim karşılığı',
    '/sozluk/{kelime}': 'TDK sözlük anlamı',
    '/cevir?q=hello&to=tr': 'Metin çeviri (en fazla 500 karakter)',
    '/romen/{sayı}': 'Sayı <-> romen rakamı çevirici',
    '/yaziyla/{tutar}': 'Tutarı yazıya çevirir (çek/senet yazısı)',
    '/loto/{oyun}': 'Rastgele loto kolonu (sayisal, sanstopu, onnumara, superloto)',
    '/rastgele/{min}/{max}': 'Rastgele sayı (?adet=5&tekrarsiz=1)',
    '/sec?liste=a,b,c': 'Seçenekler arasından rastgele seçim yapar',
    '/atasozu': 'Rastgele atasözü ve anlamı (?gunluk=1 günün atasözü)',
  },
  hesaplamalar: {
    '/yas/{yyyy-aa-gg}': 'Yaş hesaplama, toplam gün, sonraki doğum günü, burç',
    '/tarihfark/{baslangic}/{bitis}': 'İki tarih arası gün, hafta, ay, iş günü sayısı (bitiş boşsa bugün)',
    '/bmi/{boy_cm}/{kilo_kg}': 'Vücut kitle indeksi ve kategori',
    '/birim/{deger}/{from}/{to}': 'Birim çevirici (örn. /birim/100/km/mi, tüm birimler için /birim)',
  },
  gunluk_ek: {
    '/gno?dersler=AA:3,BB:4': 'Not ortalaması (GNO), harf veya puan ile',
    '/gecmenotu/{vize}': 'Geçmek için finalden gereken not',
    '/boya/{en}/{boy}/{yukseklik}': 'Boya, parke ve fayans miktarı',
    '/elektrik/{watt}/{saat}?fiyat=3.2': 'Cihazın elektrik maliyeti',
    '/klima/{m2}': 'Klima BTU önerisi',
    '/tuketim/{deger}/{from}/{to}': 'Yakıt tüketimi çevirici (l100, kml, mpg, mpguk)',
    '/tarihyazi/{tarih}': 'Tarihi yazıyla yazar',
    '/telefon/{numara}': 'Telefon doğrulama ve biçimlendirme',
    '/dilekce?konu=...': 'Dilekçe taslağı',
    '/mesaj/{tur}': 'Kutlama mesajı (bayram, dogumgunu, gecmisolsun...)',
    '/hesapla?ifade=2*(3+4)': 'Matematik ifadesi hesaplama',
    '/aktivite/{tur}/{dakika}': 'Yakılan kalori',
    '/yemek/{ogun}?malzeme=patates': 'Ne pişirsem önerisi',
    '/giyim/{sehir}': 'Hava durumuna göre ne giymeli',
    '/varis/{km}/{hiz}': 'Varış saati hesaplama',
    '/zekat/{varlik}?nisap=250000': 'Zekat hesaplama',
  },
  bot_komutlari: {
    '/etkilesim/{eylem}?kim=Ahmet&kime=Ayşe': 'op, saril, tokat, elsik, selam, dans, agla, gul, alkis, durt, oksa (gif=1 ile gif)',
    '/ship/{isim1}/{isim2}': 'Uyum yüzdesi',
    '/8top?soru=...': 'Sihirli 8 top',
    '/dogruluk-cesaret/{tur}': 'Doğruluk veya cesaret',
    '/fal/{burc}': 'Günlük fal',
    '/iltifat': 'Rastgele iltifat',
    '/espri/{tur}': 'Espri veya fıkra',
    '/bilmece': 'Bilmece',
    '/quiz/{kategori}': 'Bilgi yarışması sorusu (cografya, tarih, genel)',
    '/adamasmaca/{zorluk}': 'Adam asmaca kelimesi',
    '/wordle?gunluk=1&tahmin=kalem': 'Wordle kelimesi ve tahmin değerlendirme',
    '/tkm/{hamle}': 'Taş kağıt makas',
    '/kart': 'Kart çek, /kart/poker ile poker eli',
    '/takmaad/{tur}': 'Oyuncu, klan, sunucu adı',
    '/karakter': 'RPG karakteri',
    '/hediye/{kisi}': 'Hediye önerisi',
  },
  yazilimci: {
    '/sahte/kisi?adet=3': 'Test için sahte kişi (geçerli TCKN, IBAN)',
    '/cron?ifade=*/15 9-17 * * 1-5': 'Cron açıklaması ve sonraki çalışma zamanları',
    '/durumkodu/{kod}': 'HTTP durum kodu açıklaması',
    '/cidr/{ag}': 'CIDR / subnet hesabı',
    '/ua': 'User-Agent çözümleyici',
    '/lorem/{paragraf}': 'Türkçe lorem ipsum',
    '/json?q={...}': 'JSON doğrula, güzelleştir, küçült',
    '/regex?desen=...&metin=...': 'Regex test',
    '/metinstil/{stil}?q=...': 'Metin araçları (buyuk, ters, slug, mors, binary...)',
    '/epostakontrol/{adres}': 'E-posta biçimi, MX ve tek kullanımlık adres kontrolü',
  },
  not: 'Metin içinde ? & # / varsa kodla (%3F %26 %23 %2F) ya da ?text=... kullan',
  examples: ['/whois/google.com', '/ip/8.8.8.8', '/ssl/github.com', '/iban/TR330006100519786457841326', '/qr/https%3A%2F%2Fexample.com'],
  configuration: {
    PORT: 'İsteğe bağlı HTTP portu',
    TRUST_PROXY: 'İsteğe bağlı; güvenilir proxy arkasında 1 olarak ayarlayın',
  },
  rate_limit: `${LIMIT} istek/dk`,
};

function clientIp(req) {
  const raw = TRUST_PROXY ? (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0] : (req.socket.remoteAddress || '');
  return raw.trim().replace(/^::ffff:/, '');
}

// Vercel Serverless Function Handler
module.exports = async (req, res) => {
  try {
    if (!['GET', 'HEAD', 'POST'].includes(req.method)) {
      res.writeHead(405, { allow: 'GET, HEAD, POST', ...CORS });
      return res.end();
    }

    const ip = clientIp(req);
    const now = Date.now();
    const h = (hits.get(ip) || []).filter((t) => now - t < 60000);
    h.push(now);
    hits.set(ip, h);
    if (h.length > LIMIT) return send(res, 429, { error: 'Çok fazla istek, biraz bekleyin.' });

    const u = new URL(req.url, 'http://x');
    const [, name, ...rest] = u.pathname.split('/');
    if (!name) {
      const wantsHtml = PORTAL && /text\/html/.test(req.headers.accept || '') && u.searchParams.get('format') !== 'text';
      if (wantsHtml) {
        res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'public, max-age=300', ...CORS });
        return res.end(req.method === 'HEAD' ? undefined : PORTAL);
      }
      return send(res, 200, DOCS);
    }

    const route = ROUTES[name];
    if (!route) return send(res, 404, { error: 'Bulunamadı. Endpoint listesi için: /' });
    if (req.method === 'POST' && (name !== 'tempmail' || (rest[0] && rest[0] !== 'new'))) {
      res.writeHead(405, { allow: 'GET, HEAD, POST', ...CORS });
      return res.end();
    }

    const ctx = { u, req, ip, rest, q: (k) => u.searchParams.get(k) };
    let result, cacheKey = null;

    if (route.custom) {
      result = await route.run(null, ctx);
    } else {
      let arg = rest.join('/') || ctx.q('q') || '';
      if (name === 'expand' && rest.length) {
        arg = (/^https?%3A/i.test(rest[0]) ? dec(arg) : arg) + u.search;
      }
      if (!arg) return send(res, 400, { error: `Kullanım: /${name}/{${route.param}}` });
      const target = route.clean(arg);
      if (!target) return send(res, 400, { error: route.bad || 'Geçersiz değer' });

      if (route.cache) {
        cacheKey = `${name}:${target}`;
        const hit = cache.get(cacheKey);
        if (hit && Date.now() - hit.at < CACHE_TTL) return send(res, 200, { ...hit.data, cached: true });
      }
      result = await route.run(target, ctx);
      if (cacheKey) cache.set(cacheKey, { at: Date.now(), data: result });
      return send(res, 200, route.cache ? { ...result, cached: false } : result);
    }

    if (result.__raw) return sendRaw(res, result.type, result.body);
    if (result.__json) return sendJson(res, result.status || 200, result.body);
    send(res, 200, result);
  } catch (e) {
    send(res, e.status || 500, { error: e.status ? e.message : 'Sunucu hatası' });
  }
};

// Yerel bilgisayarda çalıştırmak istersen: node api/index.js
if (!process.env.VERCEL) {
  http.createServer(module.exports).listen(PORT, () => console.log(`API http://localhost:${PORT}`));
}

// Tarayıcıdan / adresine girilince gösterilen dokümantasyon sayfası (APITR portalı)
var PORTAL = Buffer.from("<!DOCTYPE html>\n<html lang=\"tr\" class=\"dark\">\n<head>\n    <meta charset=\"UTF-8\">\n    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n    <title>APITR | API Portal & Dokümantasyonu</title>\n    <link rel=\"icon\" type=\"image/png\" href=\"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAG6klEQVR42u2bX0hT4RvHn3PO/uTcVCaGlU1JKJJqBAUVgpFRJHhREdiN0G0QXkQFUaFXXShRUXSR4UVFeBFYEARdeFGEWDEKGcxWy1yO/XFt56xt5+yc8/3d/M75ueb4mW4T3V4Yvhy3c/x83+/zPO/7MBn6twFaG4Mp5BvXCvSyGNl1Dv9/GZh1DL4kXraM4BdlY8sIflFGlsp8sGW2+jmsbBnCZ4lQCYFyF4ApU/tXHFARoCJARYDVE4BlWWIYhtra2ujBgwf6tdXcEJT0xXEciAjPnz8HABw9ejTreolfqwN/9uxZAIAsy/D5fLBarWBZFgzDrF8BWJYFy7JoaGhAKBSCoiiQJAkAcPv2bRARDAbD+hVAg3vy5Im++tpPVVVx8ODB1QiF0lq/u7s7C37h/MuXLzCZTOA4rpShUPyHMAwDlmVRV1cHv98PVVWhKAoWjkwmAwC4fv16qUOhdNYfHh7Ogl04VFWFLMtIp9Noa2vTc8aaF0Cz/rFjxxaFV1U1JxTevn0LhmFKFQrFtT7HcbBarfj+/fui1v97aAKdP3++VAmx+Na/e/duzuqrqgpVVSEIgj7XriuKgng8jqamJj1/rDkBtJU7dOiQHt8apGb1sbExdHR0AECWMxb+vgQuKJ71TSYTpqamsgA1MURRxK5du0BEGB0dzVsaT58+XWwRimf9gYGBHOtr85s3b+pgTU1N4HkeiqLoLtHms7OzqKmpKeY2uTjW3717NyRJyrK+BuXz+VBdXQ2WZWE0GkFEuHz5cl4X3Llzp5guKLz1WZbF+/fv8wKdPHlSB1oYLm63G6qqIpPJQFEUPVREUcTevXuLJULhV7+vry/H+hr8q1evckC0+fHjx/OWR6/Xi7q6OphMJhiNRhgMhoKIUbCuMMuyBIAcDgdNTU2RxWIhhmGIYRgCQABIkiTas2cPffv2jTiOIwBZn5ckiR4/fkzt7e0UDocpkUhQNBqlSCRCgiDQ0NAQBYPB7LY2w5DVaiVBEFa3Lc5xHCmKQi9fvqTu7m5SFIU4jiMiIlmWyWAwUH9/Pw0MDBDLsqSqav4/6r+icRxHZrOZLBYL2Ww2cjgc1NjYSJs2baLW1lZqbm4mv99Pjx49IpfLpQtdcgE0+J6eHnr27JkOTESkqioxDENer5ecTielUinasGEDtbe309atW6mxsZEaGhqovr6e6uvryWazkdVqpdraWrLZbGSxWKiqqkoXUxvT09M0PDxMIyMjFIlEdNFK3hLTmhx2ux2BQACKoiy6qTlx4gSICDU1NXj37h2WMyYnJ3Hx4kW0tLTkJN9VS4J/n/QWy/qjo6P6+7VmSCKRgCRJyGQyyGQyEEUR6XQ6SzxFUTAxMYFLly5hx44dMBgMaG5u1nuIBoOhEHuDlWf9w4cP58Bre/pYLAaHwwEiwoULFwAAsVgMoijq8AtPhKqqYmJiAlevXoXT6YTZbMa2bdvQ29uLhw8fwuVyQRAEdHZ2Fqosrqzmm81muN3urNbWwhLY19cHIkJHRwd4nsf8/DxisRhSqVSWvV0uF27cuAGn06k/o6WlBU+fPsWbN2/w8eNHeL1e+Hw+BAIBTE5OoqqqqhA7xJVZv7+/HwAgimLW5gUAPnz4AJZlsXnzZnz+/BnhcBiCIOjQHo8Hg4ODOHDgQBYEwzAwGo2wWCwYGRnB9PQ0PB4Pfvz4gZmZGczMzEAURb17tEIXLC/xERF27tyJVCqFTCaTE8+yLGPfvn0gIoyNjUGWZfA8D7fbjfv376OzsxNmszlHVO3eGtT+/fsRDofh8/nw8+dPzM3NIRAIIBKJgOf5QnSPlh/74+PjAIB0Oq3DJ5NJAMC9e/dARBgaGsLXr19x69YtdHV1wWq15oXO95zBwUGkUinMzs4iGAwiHA4jEolAlmW8fv16pS5YnvXPnTsHAFkOSKfTkGUZfr8f1dXV2LJlC06dOoXa2tocsKW0u7RmiN1uh8fjQSwWQyQSQSwWQzweRzQaBQD09vauRIR/t//GjRsRDod1u0uSBEmS9MTW09OTY8ulQudzwZkzZwAA0WgUPM9DEAS9lP769Qt2u325YfDvttFqfjKZzIFfaMlCNTY1EV68eAEAiMfjSCaTSKVSSCQSWUfmogvQ1dWllzlZliHLsn585Xke27dvL3gfTyt1ra2tiMfj+pFZ6yVqe44jR44UX4BPnz7hz58/+P37N+LxOOLxOObn55FMJnHt2rWiNS60e165cgXRaBRzc3MIhUIIhUIIBoOIRqMYHx9fveNw5QsSFQEqAlQEWKsCMGXMz1QcUBHgf83RsrP/3w5gyg2+EgKLCMCU0+rncwBTLvBLgcV6BV9qDmDWM/xyANfdv8//B13L5kNuCAylAAAAAElFTkSuQmCC\">\n    <!-- Tailwind CSS -->\n    <link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n    <link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n    <link href=\"https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@400;500;600&display=swap\" rel=\"stylesheet\">\n    <style>\n*,:after,:before{--tw-border-spacing-x:0;--tw-border-spacing-y:0;--tw-translate-x:0;--tw-translate-y:0;--tw-rotate:0;--tw-skew-x:0;--tw-skew-y:0;--tw-scale-x:1;--tw-scale-y:1;--tw-pan-x: ;--tw-pan-y: ;--tw-pinch-zoom: ;--tw-scroll-snap-strictness:proximity;--tw-gradient-from-position: ;--tw-gradient-via-position: ;--tw-gradient-to-position: ;--tw-ordinal: ;--tw-slashed-zero: ;--tw-numeric-figure: ;--tw-numeric-spacing: ;--tw-numeric-fraction: ;--tw-ring-inset: ;--tw-ring-offset-width:0px;--tw-ring-offset-color:#fff;--tw-ring-color:rgba(59,130,246,.5);--tw-ring-offset-shadow:0 0 #0000;--tw-ring-shadow:0 0 #0000;--tw-shadow:0 0 #0000;--tw-shadow-colored:0 0 #0000;--tw-blur: ;--tw-brightness: ;--tw-contrast: ;--tw-grayscale: ;--tw-hue-rotate: ;--tw-invert: ;--tw-saturate: ;--tw-sepia: ;--tw-drop-shadow: ;--tw-backdrop-blur: ;--tw-backdrop-brightness: ;--tw-backdrop-contrast: ;--tw-backdrop-grayscale: ;--tw-backdrop-hue-rotate: ;--tw-backdrop-invert: ;--tw-backdrop-opacity: ;--tw-backdrop-saturate: ;--tw-backdrop-sepia: ;--tw-contain-size: ;--tw-contain-layout: ;--tw-contain-paint: ;--tw-contain-style: }::backdrop{--tw-border-spacing-x:0;--tw-border-spacing-y:0;--tw-translate-x:0;--tw-translate-y:0;--tw-rotate:0;--tw-skew-x:0;--tw-skew-y:0;--tw-scale-x:1;--tw-scale-y:1;--tw-pan-x: ;--tw-pan-y: ;--tw-pinch-zoom: ;--tw-scroll-snap-strictness:proximity;--tw-gradient-from-position: ;--tw-gradient-via-position: ;--tw-gradient-to-position: ;--tw-ordinal: ;--tw-slashed-zero: ;--tw-numeric-figure: ;--tw-numeric-spacing: ;--tw-numeric-fraction: ;--tw-ring-inset: ;--tw-ring-offset-width:0px;--tw-ring-offset-color:#fff;--tw-ring-color:rgba(59,130,246,.5);--tw-ring-offset-shadow:0 0 #0000;--tw-ring-shadow:0 0 #0000;--tw-shadow:0 0 #0000;--tw-shadow-colored:0 0 #0000;--tw-blur: ;--tw-brightness: ;--tw-contrast: ;--tw-grayscale: ;--tw-hue-rotate: ;--tw-invert: ;--tw-saturate: ;--tw-sepia: ;--tw-drop-shadow: ;--tw-backdrop-blur: ;--tw-backdrop-brightness: ;--tw-backdrop-contrast: ;--tw-backdrop-grayscale: ;--tw-backdrop-hue-rotate: ;--tw-backdrop-invert: ;--tw-backdrop-opacity: ;--tw-backdrop-saturate: ;--tw-backdrop-sepia: ;--tw-contain-size: ;--tw-contain-layout: ;--tw-contain-paint: ;--tw-contain-style: }/*! tailwindcss v3.4.17 | MIT License | https://tailwindcss.com*/*,:after,:before{box-sizing:border-box;border:0 solid #e5e5e5}:after,:before{--tw-content:\"\"}:host,html{line-height:1.5;-webkit-text-size-adjust:100%;-moz-tab-size:4;-o-tab-size:4;tab-size:4;font-family:Inter,sans-serif;font-feature-settings:normal;font-variation-settings:normal;-webkit-tap-highlight-color:transparent}body{margin:0;line-height:inherit}hr{height:0;color:inherit;border-top-width:1px}abbr:where([title]){-webkit-text-decoration:underline dotted;text-decoration:underline dotted}h1,h2,h3,h4,h5,h6{font-size:inherit;font-weight:inherit}a{color:inherit;text-decoration:inherit}b,strong{font-weight:bolder}code,kbd,pre,samp{font-family:JetBrains Mono,Fira Code,Consolas,monospace;font-feature-settings:normal;font-variation-settings:normal;font-size:1em}small{font-size:80%}sub,sup{font-size:75%;line-height:0;position:relative;vertical-align:baseline}sub{bottom:-.25em}sup{top:-.5em}table{text-indent:0;border-color:inherit;border-collapse:collapse}button,input,optgroup,select,textarea{font-family:inherit;font-feature-settings:inherit;font-variation-settings:inherit;font-size:100%;font-weight:inherit;line-height:inherit;letter-spacing:inherit;color:inherit;margin:0;padding:0}button,select{text-transform:none}button,input:where([type=button]),input:where([type=reset]),input:where([type=submit]){-webkit-appearance:button;background-color:transparent;background-image:none}:-moz-focusring{outline:auto}:-moz-ui-invalid{box-shadow:none}progress{vertical-align:baseline}::-webkit-inner-spin-button,::-webkit-outer-spin-button{height:auto}[type=search]{-webkit-appearance:textfield;outline-offset:-2px}::-webkit-search-decoration{-webkit-appearance:none}::-webkit-file-upload-button{-webkit-appearance:button;font:inherit}summary{display:list-item}blockquote,dd,dl,figure,h1,h2,h3,h4,h5,h6,hr,p,pre{margin:0}fieldset{margin:0}fieldset,legend{padding:0}menu,ol,ul{list-style:none;margin:0;padding:0}dialog{padding:0}textarea{resize:vertical}input::-moz-placeholder,textarea::-moz-placeholder{opacity:1;color:#a3a3a3}input::placeholder,textarea::placeholder{opacity:1;color:#a3a3a3}[role=button],button{cursor:pointer}:disabled{cursor:default}audio,canvas,embed,iframe,img,object,svg,video{display:block;vertical-align:middle}img,video{max-width:100%;height:auto}[hidden]:where(:not([hidden=until-found])){display:none}.container{width:100%}@media (min-width:640px){.container{max-width:640px}}@media (min-width:768px){.container{max-width:768px}}@media (min-width:1024px){.container{max-width:1024px}}@media (min-width:1280px){.container{max-width:1280px}}@media (min-width:1536px){.container{max-width:1536px}}.pointer-events-none{pointer-events:none}.fixed{position:fixed}.absolute{position:absolute}.relative{position:relative}.sticky{position:sticky}.-bottom-10{bottom:-2.5rem}.-right-10{right:-2.5rem}.bottom-0{bottom:0}.bottom-6{bottom:1.5rem}.left-0{left:0}.left-3{left:.75rem}.right-3{right:.75rem}.right-4{right:1rem}.right-6{right:1.5rem}.top-0{top:0}.top-1\\/2{top:50%}.top-16{top:4rem}.top-24{top:6rem}.top-3{top:.75rem}.z-10{z-index:10}.z-30{z-index:30}.z-40{z-index:40}.z-50{z-index:50}.mx-auto{margin-left:auto;margin-right:auto}.mb-1{margin-bottom:.25rem}.mb-2{margin-bottom:.5rem}.mb-3{margin-bottom:.75rem}.mb-4{margin-bottom:1rem}.ml-2{margin-left:.5rem}.mt-0\\.5{margin-top:.125rem}.mt-1{margin-top:.25rem}.mt-4{margin-top:1rem}.block{display:block}.flex{display:flex}.inline-flex{display:inline-flex}.hidden{display:none}.h-12{height:3rem}.h-16{height:4rem}.h-3\\.5{height:.875rem}.h-36{height:9rem}.h-4{height:1rem}.h-5{height:1.25rem}.h-6{height:1.5rem}.h-64{height:16rem}.h-9{height:2.25rem}.min-h-screen{min-height:100vh}.w-12{width:3rem}.w-3\\.5{width:.875rem}.w-4{width:1rem}.w-5{width:1.25rem}.w-6{width:1.5rem}.w-64{width:16rem}.w-72{width:18rem}.w-auto{width:auto}.w-fit{width:-moz-fit-content;width:fit-content}.w-full{width:100%}.min-w-0{min-width:0}.max-w-2xl{max-width:42rem}.max-w-7xl{max-width:80rem}.flex-1{flex:1 1 0%}.shrink-0{flex-shrink:0}.-translate-x-full{--tw-translate-x:-100%}.-translate-x-full,.-translate-y-1\\/2{transform:translate(var(--tw-translate-x),var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.-translate-y-1\\/2{--tw-translate-y:-50%}.translate-y-20{--tw-translate-y:5rem}.rotate-180,.translate-y-20{transform:translate(var(--tw-translate-x),var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.rotate-180{--tw-rotate:180deg}.transform{transform:translate(var(--tw-translate-x),var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.select-none{-webkit-user-select:none;-moz-user-select:none;user-select:none}.flex-col{flex-direction:column}.flex-wrap{flex-wrap:wrap}.items-center{align-items:center}.justify-center{justify-content:center}.justify-between{justify-content:space-between}.gap-1{gap:.25rem}.gap-1\\.5{gap:.375rem}.gap-2{gap:.5rem}.gap-2\\.5{gap:.625rem}.gap-3{gap:.75rem}.gap-8{gap:2rem}.space-y-0\\.5>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(.125rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(.125rem*var(--tw-space-y-reverse))}.space-y-1>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(.25rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(.25rem*var(--tw-space-y-reverse))}.space-y-2>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(.5rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(.5rem*var(--tw-space-y-reverse))}.space-y-3>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(.75rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(.75rem*var(--tw-space-y-reverse))}.space-y-4>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(1rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(1rem*var(--tw-space-y-reverse))}.space-y-6>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(1.5rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(1.5rem*var(--tw-space-y-reverse))}.overflow-hidden{overflow:hidden}.overflow-x-auto{overflow-x:auto}.overflow-y-auto{overflow-y:auto}.truncate{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.rounded{border-radius:.25rem}.rounded-2xl{border-radius:1rem}.rounded-3xl{border-radius:1.5rem}.rounded-full{border-radius:9999px}.rounded-lg{border-radius:.5rem}.rounded-md{border-radius:.375rem}.rounded-xl{border-radius:.75rem}.border{border-width:1px}.border-b{border-bottom-width:1px}.border-l-4{border-left-width:4px}.border-r{border-right-width:1px}.border-t{border-top-width:1px}.border-black{--tw-border-opacity:1;border-color:rgb(0 0 0/var(--tw-border-opacity,1))}.border-emerald-400\\/30{border-color:rgba(52,211,153,.3)}.border-gray-100{--tw-border-opacity:1;border-color:rgb(245 245 245/var(--tw-border-opacity,1))}.border-gray-200{--tw-border-opacity:1;border-color:rgb(229 229 229/var(--tw-border-opacity,1))}.border-gray-200\\/50{border-color:hsla(0,0%,90%,.5)}.border-gray-200\\/70{border-color:hsla(0,0%,90%,.7)}.border-gray-200\\/80{border-color:hsla(0,0%,90%,.8)}.border-gray-300{--tw-border-opacity:1;border-color:rgb(212 212 212/var(--tw-border-opacity,1))}.border-gray-800{--tw-border-opacity:1;border-color:rgb(38 38 38/var(--tw-border-opacity,1))}.border-white\\/10{border-color:hsla(0,0%,100%,.1)}.border-white\\/20{border-color:hsla(0,0%,100%,.2)}.border-l-emerald-500{--tw-border-opacity:1;border-left-color:rgb(16 185 129/var(--tw-border-opacity,1))}.bg-black{--tw-bg-opacity:1;background-color:rgb(0 0 0/var(--tw-bg-opacity,1))}.bg-emerald-500{--tw-bg-opacity:1;background-color:rgb(16 185 129/var(--tw-bg-opacity,1))}.bg-emerald-500\\/15{background-color:rgba(16,185,129,.15)}.bg-gray-100{--tw-bg-opacity:1;background-color:rgb(245 245 245/var(--tw-bg-opacity,1))}.bg-gray-100\\/70{background-color:hsla(0,0%,96%,.7)}.bg-gray-200{--tw-bg-opacity:1;background-color:rgb(229 229 229/var(--tw-bg-opacity,1))}.bg-gray-200\\/60{background-color:hsla(0,0%,90%,.6)}.bg-gray-300{--tw-bg-opacity:1;background-color:rgb(212 212 212/var(--tw-bg-opacity,1))}.bg-gray-50{--tw-bg-opacity:1;background-color:rgb(250 250 250/var(--tw-bg-opacity,1))}.bg-gray-50\\/30{background-color:hsla(0,0%,98%,.3)}.bg-gray-800{--tw-bg-opacity:1;background-color:rgb(38 38 38/var(--tw-bg-opacity,1))}.bg-gray-900{--tw-bg-opacity:1;background-color:rgb(23 23 23/var(--tw-bg-opacity,1))}.bg-white{--tw-bg-opacity:1;background-color:rgb(255 255 255/var(--tw-bg-opacity,1))}.bg-white\\/10{background-color:hsla(0,0%,100%,.1)}.bg-white\\/5{background-color:hsla(0,0%,100%,.05)}.bg-white\\/80{background-color:hsla(0,0%,100%,.8)}.bg-gradient-to-br{background-image:linear-gradient(to bottom right,var(--tw-gradient-stops))}.from-neutral-900{--tw-gradient-from:#171717 var(--tw-gradient-from-position);--tw-gradient-to:hsla(0,0%,9%,0) var(--tw-gradient-to-position);--tw-gradient-stops:var(--tw-gradient-from),var(--tw-gradient-to)}.to-black{--tw-gradient-to:#000 var(--tw-gradient-to-position)}.p-1{padding:.25rem}.p-1\\.5{padding:.375rem}.p-12{padding:3rem}.p-2{padding:.5rem}.p-2\\.5{padding:.625rem}.p-3{padding:.75rem}.p-4{padding:1rem}.p-5{padding:1.25rem}.p-6{padding:1.5rem}.px-1\\.5{padding-left:.375rem;padding-right:.375rem}.px-2{padding-left:.5rem;padding-right:.5rem}.px-2\\.5{padding-left:.625rem;padding-right:.625rem}.px-3{padding-left:.75rem;padding-right:.75rem}.px-3\\.5{padding-left:.875rem;padding-right:.875rem}.px-4{padding-left:1rem;padding-right:1rem}.py-0\\.5{padding-top:.125rem;padding-bottom:.125rem}.py-1{padding-top:.25rem;padding-bottom:.25rem}.py-1\\.5{padding-top:.375rem;padding-bottom:.375rem}.py-2{padding-top:.5rem;padding-bottom:.5rem}.py-2\\.5{padding-top:.625rem;padding-bottom:.625rem}.py-3{padding-top:.75rem;padding-bottom:.75rem}.py-8{padding-top:2rem;padding-bottom:2rem}.pl-9{padding-left:2.25rem}.pr-4{padding-right:1rem}.text-left{text-align:left}.text-center{text-align:center}.font-mono{font-family:JetBrains Mono,Fira Code,Consolas,monospace}.text-2xl{font-size:1.5rem;line-height:2rem}.text-\\[10px\\]{font-size:10px}.text-base{font-size:1rem;line-height:1.5rem}.text-lg{font-size:1.125rem;line-height:1.75rem}.text-sm{font-size:.875rem;line-height:1.25rem}.text-xs{font-size:.75rem;line-height:1rem}.font-bold{font-weight:700}.font-extrabold{font-weight:800}.font-medium{font-weight:500}.font-semibold{font-weight:600}.uppercase{text-transform:uppercase}.leading-relaxed{line-height:1.625}.tracking-\\[0\\.25em\\]{letter-spacing:.25em}.tracking-tight{letter-spacing:-.025em}.tracking-wide{letter-spacing:.025em}.tracking-wider{letter-spacing:.05em}.text-black{--tw-text-opacity:1;color:rgb(0 0 0/var(--tw-text-opacity,1))}.text-emerald-300{--tw-text-opacity:1;color:rgb(110 231 183/var(--tw-text-opacity,1))}.text-emerald-500{--tw-text-opacity:1;color:rgb(16 185 129/var(--tw-text-opacity,1))}.text-emerald-600{--tw-text-opacity:1;color:rgb(5 150 105/var(--tw-text-opacity,1))}.text-gray-100{--tw-text-opacity:1;color:rgb(245 245 245/var(--tw-text-opacity,1))}.text-gray-300{--tw-text-opacity:1;color:rgb(212 212 212/var(--tw-text-opacity,1))}.text-gray-400{--tw-text-opacity:1;color:rgb(163 163 163/var(--tw-text-opacity,1))}.text-gray-500{--tw-text-opacity:1;color:rgb(115 115 115/var(--tw-text-opacity,1))}.text-gray-600{--tw-text-opacity:1;color:rgb(82 82 82/var(--tw-text-opacity,1))}.text-gray-700{--tw-text-opacity:1;color:rgb(64 64 64/var(--tw-text-opacity,1))}.text-gray-800{--tw-text-opacity:1;color:rgb(38 38 38/var(--tw-text-opacity,1))}.text-gray-900{--tw-text-opacity:1;color:rgb(23 23 23/var(--tw-text-opacity,1))}.text-red-500{--tw-text-opacity:1;color:rgb(239 68 68/var(--tw-text-opacity,1))}.text-white{--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.antialiased{-webkit-font-smoothing:antialiased;-moz-osx-font-smoothing:grayscale}.opacity-0{opacity:0}.opacity-10{opacity:.1}.shadow-md{--tw-shadow:0 4px 6px -1px rgba(0,0,0,.1),0 2px 4px -2px rgba(0,0,0,.1);--tw-shadow-colored:0 4px 6px -1px var(--tw-shadow-color),0 2px 4px -2px var(--tw-shadow-color)}.shadow-md,.shadow-sm{box-shadow:var(--tw-ring-offset-shadow,0 0 #0000),var(--tw-ring-shadow,0 0 #0000),var(--tw-shadow)}.shadow-sm{--tw-shadow:0 1px 2px 0 rgba(0,0,0,.05);--tw-shadow-colored:0 1px 2px 0 var(--tw-shadow-color)}.shadow-xl{--tw-shadow:0 20px 25px -5px rgba(0,0,0,.1),0 8px 10px -6px rgba(0,0,0,.1);--tw-shadow-colored:0 20px 25px -5px var(--tw-shadow-color),0 8px 10px -6px var(--tw-shadow-color);box-shadow:var(--tw-ring-offset-shadow,0 0 #0000),var(--tw-ring-shadow,0 0 #0000),var(--tw-shadow)}.blur{--tw-blur:blur(8px)}.blur,.blur-3xl{filter:var(--tw-blur) var(--tw-brightness) var(--tw-contrast) var(--tw-grayscale) var(--tw-hue-rotate) var(--tw-invert) var(--tw-saturate) var(--tw-sepia) var(--tw-drop-shadow)}.blur-3xl{--tw-blur:blur(64px)}.invert{--tw-invert:invert(100%)}.filter,.invert{filter:var(--tw-blur) var(--tw-brightness) var(--tw-contrast) var(--tw-grayscale) var(--tw-hue-rotate) var(--tw-invert) var(--tw-saturate) var(--tw-sepia) var(--tw-drop-shadow)}.backdrop-blur-md{--tw-backdrop-blur:blur(12px)}.backdrop-blur-md,.backdrop-filter{-webkit-backdrop-filter:var(--tw-backdrop-blur) var(--tw-backdrop-brightness) var(--tw-backdrop-contrast) var(--tw-backdrop-grayscale) var(--tw-backdrop-hue-rotate) var(--tw-backdrop-invert) var(--tw-backdrop-opacity) var(--tw-backdrop-saturate) var(--tw-backdrop-sepia);backdrop-filter:var(--tw-backdrop-blur) var(--tw-backdrop-brightness) var(--tw-backdrop-contrast) var(--tw-backdrop-grayscale) var(--tw-backdrop-hue-rotate) var(--tw-backdrop-invert) var(--tw-backdrop-opacity) var(--tw-backdrop-saturate) var(--tw-backdrop-sepia)}.transition{transition-property:color,background-color,border-color,text-decoration-color,fill,stroke,opacity,box-shadow,transform,filter,-webkit-backdrop-filter;transition-property:color,background-color,border-color,text-decoration-color,fill,stroke,opacity,box-shadow,transform,filter,backdrop-filter;transition-property:color,background-color,border-color,text-decoration-color,fill,stroke,opacity,box-shadow,transform,filter,backdrop-filter,-webkit-backdrop-filter;transition-timing-function:cubic-bezier(.4,0,.2,1);transition-duration:.15s}.transition-all{transition-property:all;transition-timing-function:cubic-bezier(.4,0,.2,1);transition-duration:.15s}.transition-colors{transition-property:color,background-color,border-color,text-decoration-color,fill,stroke;transition-timing-function:cubic-bezier(.4,0,.2,1);transition-duration:.15s}.transition-transform{transition-property:transform;transition-timing-function:cubic-bezier(.4,0,.2,1);transition-duration:.15s}.duration-200{transition-duration:.2s}.duration-300{transition-duration:.3s}.ease-in-out{transition-timing-function:cubic-bezier(.4,0,.2,1)}.selection\\:bg-neutral-500 ::-moz-selection{--tw-bg-opacity:1;background-color:rgb(115 115 115/var(--tw-bg-opacity,1))}.selection\\:bg-neutral-500 ::selection{--tw-bg-opacity:1;background-color:rgb(115 115 115/var(--tw-bg-opacity,1))}.selection\\:text-white ::-moz-selection{--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.selection\\:text-white ::selection{--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.selection\\:bg-neutral-500::-moz-selection{--tw-bg-opacity:1;background-color:rgb(115 115 115/var(--tw-bg-opacity,1))}.selection\\:bg-neutral-500::selection{--tw-bg-opacity:1;background-color:rgb(115 115 115/var(--tw-bg-opacity,1))}.selection\\:text-white::-moz-selection{--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.selection\\:text-white::selection{--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.hover\\:bg-emerald-500\\/25:hover{background-color:rgba(16,185,129,.25)}.hover\\:bg-gray-100:hover{--tw-bg-opacity:1;background-color:rgb(245 245 245/var(--tw-bg-opacity,1))}.hover\\:bg-gray-50\\/50:hover{background-color:hsla(0,0%,98%,.5)}.hover\\:bg-gray-700:hover{--tw-bg-opacity:1;background-color:rgb(64 64 64/var(--tw-bg-opacity,1))}.hover\\:bg-neutral-800:hover{--tw-bg-opacity:1;background-color:rgb(38 38 38/var(--tw-bg-opacity,1))}.hover\\:text-gray-600:hover{--tw-text-opacity:1;color:rgb(82 82 82/var(--tw-text-opacity,1))}.hover\\:text-gray-900:hover{--tw-text-opacity:1;color:rgb(23 23 23/var(--tw-text-opacity,1))}.focus\\:outline-none:focus{outline:2px solid transparent;outline-offset:2px}.focus\\:ring-2:focus{--tw-ring-offset-shadow:var(--tw-ring-inset) 0 0 0 var(--tw-ring-offset-width) var(--tw-ring-offset-color);--tw-ring-shadow:var(--tw-ring-inset) 0 0 0 calc(2px + var(--tw-ring-offset-width)) var(--tw-ring-color);box-shadow:var(--tw-ring-offset-shadow),var(--tw-ring-shadow),var(--tw-shadow,0 0 #0000)}.focus\\:ring-neutral-500:focus{--tw-ring-opacity:1;--tw-ring-color:rgb(115 115 115/var(--tw-ring-opacity,1))}.active\\:scale-95:active{--tw-scale-x:.95;--tw-scale-y:.95;transform:translate(var(--tw-translate-x),var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.dark\\:border-darkborder:is(.dark *){--tw-border-opacity:1;border-color:rgb(31 31 31/var(--tw-border-opacity,1))}.dark\\:border-gray-200:is(.dark *){--tw-border-opacity:1;border-color:rgb(229 229 229/var(--tw-border-opacity,1))}.dark\\:border-gray-700:is(.dark *){--tw-border-opacity:1;border-color:rgb(64 64 64/var(--tw-border-opacity,1))}.dark\\:border-gray-800:is(.dark *){--tw-border-opacity:1;border-color:rgb(38 38 38/var(--tw-border-opacity,1))}.dark\\:border-gray-800\\/60:is(.dark *){border-color:rgba(38,38,38,.6)}.dark\\:border-white:is(.dark *){--tw-border-opacity:1;border-color:rgb(255 255 255/var(--tw-border-opacity,1))}.dark\\:border-white\\/20:is(.dark *){border-color:hsla(0,0%,100%,.2)}.dark\\:bg-darkbg:is(.dark *){--tw-bg-opacity:1;background-color:rgb(0 0 0/var(--tw-bg-opacity,1))}.dark\\:bg-darkbg\\/80:is(.dark *){background-color:rgba(0,0,0,.8)}.dark\\:bg-darkcard:is(.dark *){--tw-bg-opacity:1;background-color:rgb(10 10 10/var(--tw-bg-opacity,1))}.dark\\:bg-gray-800:is(.dark *){--tw-bg-opacity:1;background-color:rgb(38 38 38/var(--tw-bg-opacity,1))}.dark\\:bg-gray-800\\/80:is(.dark *){background-color:rgba(38,38,38,.8)}.dark\\:bg-gray-900:is(.dark *){--tw-bg-opacity:1;background-color:rgb(23 23 23/var(--tw-bg-opacity,1))}.dark\\:bg-gray-900\\/20:is(.dark *){background-color:hsla(0,0%,9%,.2)}.dark\\:bg-gray-900\\/70:is(.dark *){background-color:hsla(0,0%,9%,.7)}.dark\\:bg-gray-900\\/80:is(.dark *){background-color:hsla(0,0%,9%,.8)}.dark\\:bg-white:is(.dark *){--tw-bg-opacity:1;background-color:rgb(255 255 255/var(--tw-bg-opacity,1))}.dark\\:bg-white\\/10:is(.dark *){background-color:hsla(0,0%,100%,.1)}.dark\\:bg-white\\/20:is(.dark *){background-color:hsla(0,0%,100%,.2)}.dark\\:text-black:is(.dark *){--tw-text-opacity:1;color:rgb(0 0 0/var(--tw-text-opacity,1))}.dark\\:text-emerald-400:is(.dark *){--tw-text-opacity:1;color:rgb(52 211 153/var(--tw-text-opacity,1))}.dark\\:text-gray-100:is(.dark *){--tw-text-opacity:1;color:rgb(245 245 245/var(--tw-text-opacity,1))}.dark\\:text-gray-200:is(.dark *){--tw-text-opacity:1;color:rgb(229 229 229/var(--tw-text-opacity,1))}.dark\\:text-gray-300:is(.dark *){--tw-text-opacity:1;color:rgb(212 212 212/var(--tw-text-opacity,1))}.dark\\:text-gray-400:is(.dark *){--tw-text-opacity:1;color:rgb(163 163 163/var(--tw-text-opacity,1))}.dark\\:text-gray-500:is(.dark *){--tw-text-opacity:1;color:rgb(115 115 115/var(--tw-text-opacity,1))}.dark\\:text-gray-900:is(.dark *){--tw-text-opacity:1;color:rgb(23 23 23/var(--tw-text-opacity,1))}.dark\\:text-white:is(.dark *){--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}.dark\\:invert-0:is(.dark *){--tw-invert:invert(0);filter:var(--tw-blur) var(--tw-brightness) var(--tw-contrast) var(--tw-grayscale) var(--tw-hue-rotate) var(--tw-invert) var(--tw-saturate) var(--tw-sepia) var(--tw-drop-shadow)}.dark\\:hover\\:bg-gray-800:hover:is(.dark *){--tw-bg-opacity:1;background-color:rgb(38 38 38/var(--tw-bg-opacity,1))}.dark\\:hover\\:bg-gray-800\\/30:hover:is(.dark *){background-color:rgba(38,38,38,.3)}.dark\\:hover\\:bg-gray-900:hover:is(.dark *){--tw-bg-opacity:1;background-color:rgb(23 23 23/var(--tw-bg-opacity,1))}.dark\\:hover\\:bg-neutral-200:hover:is(.dark *){--tw-bg-opacity:1;background-color:rgb(229 229 229/var(--tw-bg-opacity,1))}.dark\\:hover\\:text-gray-200:hover:is(.dark *){--tw-text-opacity:1;color:rgb(229 229 229/var(--tw-text-opacity,1))}.dark\\:hover\\:text-white:hover:is(.dark *){--tw-text-opacity:1;color:rgb(255 255 255/var(--tw-text-opacity,1))}@media (min-width:640px){.sm\\:block{display:block}.sm\\:inline-block{display:inline-block}.sm\\:hidden{display:none}.sm\\:h-40{height:10rem}.sm\\:w-64{width:16rem}.sm\\:flex-row{flex-direction:row}.sm\\:items-center{align-items:center}.sm\\:gap-4{gap:1rem}.sm\\:p-5{padding:1.25rem}.sm\\:p-6{padding:1.5rem}.sm\\:p-8{padding:2rem}.sm\\:px-6{padding-left:1.5rem;padding-right:1.5rem}.sm\\:text-3xl{font-size:1.875rem;line-height:2.25rem}.sm\\:text-base{font-size:1rem;line-height:1.5rem}.sm\\:text-sm{font-size:.875rem;line-height:1.25rem}}@media (min-width:768px){.md\\:flex{display:flex}.md\\:w-80{width:20rem}}@media (min-width:1024px){.lg\\:static{position:static}.lg\\:inset-y-0{top:0;bottom:0}.lg\\:hidden{display:none}.lg\\:translate-x-0{--tw-translate-x:0px;transform:translate(var(--tw-translate-x),var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.lg\\:border-r-0{border-right-width:0}.lg\\:bg-transparent{background-color:transparent}.lg\\:p-0{padding:0}.lg\\:px-8{padding-left:2rem;padding-right:2rem}}\n        body {\n            font-family: 'Inter', sans-serif;\n            transition: background-color 0.3s ease, color 0.3s ease;\n        }\n        pre, code {\n            font-family: 'JetBrains Mono', monospace;\n        }\n        /* Custom scrollbars */\n        ::-webkit-scrollbar {\n            width: 6px;\n            height: 6px;\n        }\n        ::-webkit-scrollbar-track {\n            background: transparent;\n        }\n        ::-webkit-scrollbar-thumb {\n            background: rgba(156, 163, 175, 0.3);\n            border-radius: 9999px;\n        }\n        ::-webkit-scrollbar-thumb:hover {\n            background: rgba(156, 163, 175, 0.5);\n        }\n        .backdrop-blur-md {\n            backdrop-filter: blur(12px);\n            -webkit-backdrop-filter: blur(12px);\n        }\n    </style>\n</head>\n<body class=\"bg-gray-50 text-gray-900 dark:bg-darkbg dark:text-gray-100 min-h-screen flex flex-col antialiased selection:bg-neutral-500 selection:text-white\">\n\n    <!-- Top Navigation Header -->\n    <header class=\"sticky top-0 z-40 w-full border-b border-gray-200 dark:border-darkborder bg-white/80 dark:bg-darkbg/80 backdrop-blur-md transition-colors\">\n        <div class=\"max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 h-16 flex items-center justify-between\">\n            <div class=\"flex items-center gap-3\">\n                <button id=\"mobile-menu-btn\" class=\"lg:hidden p-2 rounded-xl hover:bg-gray-100 dark:hover:bg-gray-800 transition\">\n                    <svg class=\"w-6 h-6\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M4 6h16M4 12h16M4 18h16\"/></svg>\n                </button>\n                <div class=\"flex items-center gap-2\">\n                    <img src=\"data:image/png;base64,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\" alt=\"APITR\" class=\"h-9 w-auto invert dark:invert-0 select-none\">\n                    <div>\n                        <span class=\"font-bold text-lg tracking-[0.25em] text-gray-900 dark:text-white\">APITR</span>\n                        <span class=\"ml-2 text-xs px-2 py-0.5 rounded-full font-medium bg-gray-100 text-gray-700 dark:bg-white/10 dark:text-gray-300 border border-gray-200 dark:border-white/20\">v1.0</span>\n                    </div>\n                </div>\n            </div>\n\n            <!-- Global Search & System Info -->\n            <div class=\"flex items-center gap-3 sm:gap-4\">\n                <div class=\"relative hidden sm:block w-64 md:w-80\">\n                    <input type=\"text\" id=\"endpoint-search\" placeholder=\"Endpoint veya parametre ara...\" class=\"w-full pl-9 pr-4 py-2 text-sm rounded-xl border border-gray-200 dark:border-gray-800 bg-gray-100/70 dark:bg-gray-900/70 focus:outline-none focus:ring-2 focus:ring-neutral-500 transition-all text-gray-800 dark:text-gray-200\">\n                    <svg class=\"w-4 h-4 absolute left-3 top-3 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z\"/></svg>\n                </div>\n\n                <!-- Theme Switcher Toggle Button -->\n                <button id=\"theme-toggle\" class=\"p-2.5 rounded-xl border border-gray-200 dark:border-gray-800 bg-white dark:bg-gray-900 text-gray-600 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-800 transition-all shadow-sm\">\n                    <svg id=\"theme-dark-icon\" class=\"w-5 h-5 hidden\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M12 3v1m0 16v1m9-9h-1M4 12H3m15.364 6.364l-.707-.707M6.343 6.343l-.707-.707m12.728 0l-.707.707M6.343 17.657l-.707.707M16 12a4 4 0 11-8 0 4 4 0 018 0z\"/></svg>\n                    <svg id=\"theme-light-icon\" class=\"w-5 h-5 hidden\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M20.354 15.354A9 9 0 018.646 3.646 9.003 9.003 0 0012 21a9.003 9.003 0 008.354-5.646z\"/></svg>\n                </button>\n\n                <a href=\"https://api.arsivtr.xyz\" target=\"_blank\" class=\"hidden md:flex items-center gap-1.5 text-xs font-semibold px-4 py-2 rounded-xl bg-black hover:bg-neutral-800 text-white dark:bg-white dark:hover:bg-neutral-200 dark:text-black transition shadow-md\">\n                    <span>Base URL</span>\n                    <svg class=\"w-3.5 h-3.5\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M10 6H6a2 2 0 00-2 2v10a2 2 0 002 2h10a2 2 0 002-2v-4M14 4h6m0 0v6m0-6L10 14\"/></svg>\n                </a>\n            </div>\n        </div>\n    </header>\n\n    <!-- Main Content Layout -->\n    <div class=\"max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 w-full flex-1 flex gap-8 py-8\">\n\n        <!-- Sidebar Navigation -->\n        <aside id=\"sidebar\" class=\"fixed top-16 bottom-0 lg:inset-y-0 left-0 z-30 w-72 bg-white dark:bg-darkbg lg:static lg:bg-transparent border-r lg:border-r-0 border-gray-200 dark:border-gray-800 transform -translate-x-full lg:translate-x-0 transition-transform duration-300 ease-in-out p-6 lg:p-0 flex flex-col shrink-0 overflow-y-auto\">\n            <div class=\"sm:hidden mb-4\">\n                <input type=\"text\" id=\"endpoint-search-mobile\" placeholder=\"Endpoint ara...\" class=\"w-full pl-9 pr-4 py-2 text-sm rounded-xl border border-gray-200 dark:border-gray-800 bg-gray-100 dark:bg-gray-900 focus:outline-none focus:ring-2 focus:ring-neutral-500\">\n            </div>\n\n            <div class=\"sticky top-24 space-y-6\">\n                <!-- Base URL Card -->\n                <div class=\"p-4 rounded-2xl bg-white dark:bg-darkcard border border-gray-200/80 dark:border-darkborder shadow-sm\">\n                    <span class=\"text-xs font-medium text-gray-400 uppercase tracking-wider block mb-1\">Base Host</span>\n                    <div class=\"flex items-center justify-between bg-gray-50 dark:bg-gray-900/80 p-2.5 rounded-xl border border-gray-200/50 dark:border-gray-800\">\n                        <code class=\"text-xs font-semibold text-gray-900 dark:text-gray-100 truncate\">https://api.arsivtr.xyz</code>\n                        <button onclick=\"copyToClipboard('https://api.arsivtr.xyz', this)\" class=\"text-gray-400 hover:text-gray-600 dark:hover:text-gray-200 transition p-1\" title=\"Kopyala\">\n                            <svg class=\"w-4 h-4\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z\"/></svg>\n                        </button>\n                    </div>\n                </div>\n\n                <!-- Category Links Navigation -->\n                <nav class=\"space-y-1\">\n                    <div class=\"text-xs font-bold text-gray-400 dark:text-gray-500 uppercase tracking-wider px-3 mb-2\">Kategoriler</div>\n                    <a href=\"#all\" onclick=\"filterCategory('all', this, event)\" class=\"cat-link active flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium transition bg-gray-100 dark:bg-white/10 text-black dark:text-white\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M4 6a2 2 0 012-2h2a2 2 0 012 2v2a2 2 0 01-2 2H6a2 2 0 01-2-2V6zM14 6a2 2 0 012-2h2a2 2 0 012 2v2a2 2 0 01-2 2h-2a2 2 0 01-2-2V6zM4 14a2 2 0 012-2h2a2 2 0 012 2v2a2 2 0 01-2 2H6a2 2 0 01-2-2v-2zM14 14a2 2 0 012-2h2a2 2 0 012 2v2a2 2 0 01-2 2h-2a2 2 0 01-2-2v-2z\"/></svg>\n                            Tüm Servisler\n                        </span>\n                        <span id=\"count-all\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-300 dark:bg-white/20 text-black dark:text-white\">0</span>\n                    </a>\n\n                    <a href=\"#new\" onclick=\"filterCategory('new', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-emerald-500\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M5 3v4M3 5h4M6 17v4m-2-2h4m5-16l2.286 6.857L21 12l-5.714 2.143L13 21l-2.286-6.857L5 12l5.714-2.143L13 3z\"/></svg>\n                            <span class=\"text-emerald-600 dark:text-emerald-400 font-semibold\">Yeni Eklenenler</span>\n                        </span>\n                        <span id=\"count-new\" class=\"text-xs font-bold px-2 py-0.5 rounded-full bg-emerald-500 text-white\">0</span>\n                    </a>\n                    \n                    <a href=\"#weather\" onclick=\"filterCategory('weather', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M3 15a4 4 0 004 4h9a5 5 0 10-.1-9.999 5.002 5.002 0 10-9.78 2.096A4.001 4.001 0 003 15z\"/></svg>\n                            Hava &amp; Gökyüzü\n                        </span>\n                        <span id=\"count-weather\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#money\" onclick=\"filterCategory('money', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M12 8c-1.657 0-3 .895-3 2s1.343 2 3 2 3 .895 3 2-1.343 2-3 2m0-8c1.11 0 2.08.402 2.599 1M12 8V7m0 1v8m0 0v1m0-1c-1.11 0-2.08-.402-2.599-1M21 12a9 9 0 11-18 0 9 9 0 0118 0z\"/></svg>\n                            Döviz &amp; Para\n                        </span>\n                        <span id=\"count-money\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#daily\" onclick=\"filterCategory('daily', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M13 10V3L4 14h7v7l9-11h-7z\"/></svg>\n                            Günlük Hayat\n                        </span>\n                        <span id=\"count-daily\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#calc\" onclick=\"filterCategory('calc', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M9 7h6m0 10v-3m-3 3h.01M9 17h.01M9 14h.01M12 14h.01M15 11h.01M12 11h.01M9 11h.01M7 21h10a2 2 0 002-2V5a2 2 0 00-2-2H7a2 2 0 00-2 2v14a2 2 0 002 2z\"/></svg>\n                            Hesaplama Araçları\n                        </span>\n                        <span id=\"count-calc\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#fun\" onclick=\"filterCategory('fun', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M5 3v4M3 5h4M6 17v4m-2-2h4m5-16l2.286 6.857L21 12l-5.714 2.143L13 21l-2.286-6.857L5 12l5.714-2.143L13 3z\"/></svg>\n                            Eğlence &amp; Karar\n                        </span>\n                        <span id=\"count-fun\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#bot\" onclick=\"filterCategory('bot', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M8 12h.01M12 12h.01M16 12h.01M21 12c0 4.418-4.03 8-9 8a9.863 9.863 0 01-4.255-.949L3 20l1.395-3.72C3.512 15.042 3 13.574 3 12c0-4.418 4.03-8 9-8s9 3.582 9 8z\"/></svg>\n                            Bot Komutları\n                        </span>\n                        <span id=\"count-bot\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <div class=\"text-xs font-bold text-gray-400 dark:text-gray-500 uppercase tracking-wider px-3 mt-4 mb-2\">Geliştirici</div>\n\n                    <a href=\"#dev\" onclick=\"filterCategory('dev', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4\"/></svg>\n                            Yazılımcı Araçları\n                        </span>\n                        <span id=\"count-dev\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n                    <a href=\"#network\" onclick=\"filterCategory('network', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M21 12a9 9 0 01-9 9m9-9a9 9 0 00-9-9m9 9H3m9 9a9 9 0 01-9-9m9 9c1.657 0 3-4.03 3-9s-1.343-9-3-9m0 18c-1.657 0-3-4.03-3-9s1.343-9 3-9m-9 9a9 9 0 019-9\"/></svg>\n                            Domain & Network\n                        </span>\n                        <span id=\"count-network\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#verification\" onclick=\"filterCategory('verification', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M9 12l2 2 4-4m5.618-4.016A11.955 11.955 0 0112 2.944a11.955 11.955 0 01-8.618 3.04A12.02 12.02 0 003 9c0 5.591 3.824 10.29 9 11.622 5.176-1.332 9-6.03 9-11.622 0-1.042-.133-2.052-.382-3.016z\"/></svg>\n                            Doğrulama (Verification)\n                        </span>\n                        <span id=\"count-verification\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#turkey\" onclick=\"filterCategory('turkey', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M8 7V3m8 4V3m-9 8h10M5 21h14a2 2 0 002-2V7a2 2 0 00-2-2H5a2 2 0 00-2 2v12a2 2 0 002 2z\"/></svg>\n                            Türkiye Verileri\n                        </span>\n                        <span id=\"count-turkey\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#tools\" onclick=\"filterCategory('tools', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M11 4a2 2 0 114 0v1a2 2 0 002 2h3a2 2 0 012 2v3a2 2 0 01-2 2h-1a2 2 0 100 4h1a2 2 0 012 2v3a2 2 0 01-2 2h-3a2 2 0 01-2-2v-1a2 2 0 10-4 0v1a2 2 0 01-2 2H7a2 2 0 01-2-2v-3a2 2 0 00-2-2H2a2 2 0 01-2-2v-3a2 2 0 012-2h1a2 2 0 100-4H2a2 2 0 01-2-2V7a2 2 0 012-2h3a2 2 0 002-2V4z\"/></svg>\n                            Araçlar & Kripto\n                        </span>\n                        <span id=\"count-tools\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n\n                    <a href=\"#tempmail\" onclick=\"filterCategory('tempmail', this, event)\" class=\"cat-link flex items-center justify-between px-3.5 py-2.5 rounded-xl text-sm font-medium text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-900 transition\">\n                        <span class=\"flex items-center gap-2.5\">\n                            <svg class=\"w-4 h-4 text-gray-400\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M3 8l7.89 5.26a2 2 0 002.22 0L21 8M5 19h14a2 2 0 002-2V7a2 2 0 00-2-2H5a2 2 0 00-2 2v10a2 2 0 002 2z\"/></svg>\n                            Gelişmiş Geçici E-Posta\n                        </span>\n                        <span id=\"count-tempmail\" class=\"text-xs font-semibold px-2 py-0.5 rounded-full bg-gray-200 dark:bg-gray-800 text-gray-600 dark:text-gray-400\">0</span>\n                    </a>\n                </nav>\n            </div>\n        </aside>\n\n        <!-- Main Workspace Area -->\n        <main class=\"flex-1 min-w-0 space-y-6\">\n\n            <!-- Hero Introduction -->\n            <div class=\"p-6 sm:p-8 rounded-3xl bg-gradient-to-br from-neutral-900 to-black text-white border border-white/10 shadow-xl relative overflow-hidden\">\n                <div class=\"relative z-10 max-w-2xl space-y-3\">\n                    <div class=\"flex flex-wrap items-center gap-2\">\n                        <span class=\"px-3 py-1 rounded-full bg-white/10 backdrop-blur-md text-xs font-semibold tracking-wide border border-white/20\">Açık API Servisleri</span>\n                        <button onclick=\"filterCategory('new', document.querySelector('a[href=&quot;#new&quot;]'), event); document.getElementById('endpoints-list').scrollIntoView({behavior:'smooth'})\" class=\"inline-flex items-center gap-1.5 px-3 py-1 rounded-full bg-emerald-500/15 text-emerald-300 border border-emerald-400/30 text-xs font-semibold hover:bg-emerald-500/25 transition\"><svg class=\"w-3.5 h-3.5\" fill=\"none\" viewBox=\"0 0 24 24\" stroke-width=\"1.5\" stroke=\"currentColor\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" d=\"M9.813 15.904 9 18.75l-.813-2.846a4.5 4.5 0 0 0-3.09-3.09L2.25 12l2.846-.813a4.5 4.5 0 0 0 3.09-3.09L9 5.25l.813 2.846a4.5 4.5 0 0 0 3.09 3.09L15.75 12l-2.846.813a4.5 4.5 0 0 0-3.09 3.09ZM18.259 8.715 18 9.75l-.259-1.035a3.375 3.375 0 0 0-2.455-2.456L14.25 6l1.036-.259a3.375 3.375 0 0 0 2.455-2.456L18 2.25l.259 1.035a3.375 3.375 0 0 0 2.456 2.456L21.75 6l-1.035.259a3.375 3.375 0 0 0-2.456 2.456ZM16.894 20.567 16.5 21.75l-.394-1.183a2.25 2.25 0 0 0-1.423-1.423L13.5 18.75l1.183-.394a2.25 2.25 0 0 0 1.423-1.423l.394-1.183.394 1.183a2.25 2.25 0 0 0 1.423 1.423l1.183.394-1.183.394a2.25 2.25 0 0 0-1.423 1.423Z\"/></svg><span><span id=\"hero-new-count\">0</span> yeni endpoint eklendi</span></button>\n                    </div>\n                    <h1 class=\"text-2xl sm:text-3xl font-extrabold tracking-tight\">Günlük Hayat ve Geliştiriciler İçin Ücretsiz API</h1>\n                    <p class=\"text-gray-300 text-sm leading-relaxed\">Hava, döviz, kripto, deprem, hesaplayıcılar, bot komutları ve yazılımcı araçlarından domain, IP ve doğrulama servislerine kadar. Tek tıkla tarayıcıda açın veya projenize entegre edin.</p>\n                </div>\n                <img src=\"data:image/png;base64,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\" alt=\"\" aria-hidden=\"true\" class=\"absolute right-4 top-1/2 -translate-y-1/2 h-36 sm:h-40 w-auto opacity-10 pointer-events-none select-none hidden sm:block\">\n                <!-- Decorative element -->\n                <div class=\"absolute -right-10 -bottom-10 w-64 h-64 rounded-full bg-white/5 blur-3xl pointer-events-none\"></div>\n            </div>\n\n            <!-- Endpoints Container -->\n            <div id=\"endpoints-list\" class=\"space-y-4\">\n                <!-- Endpoints rendered via JavaScript -->\n            </div>\n        </main>\n    </div>\n\n    <!-- Notification Toast -->\n    <div id=\"toast\" class=\"fixed bottom-6 right-6 z-50 transform translate-y-20 opacity-0 transition-all duration-300 pointer-events-none\">\n        <div class=\"flex items-center gap-2.5 px-4 py-3 rounded-2xl bg-gray-900 text-white dark:bg-white dark:text-gray-900 shadow-xl border border-gray-800 dark:border-gray-200 text-sm font-medium\">\n            <svg class=\"w-5 h-5 text-white dark:text-black\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M5 13l4 4L19 7\"/></svg>\n            <span id=\"toast-message\">Kopyalandı!</span>\n        </div>\n    </div>\n\n    <!-- JavaScript Application Logic -->\n    <script>\n        // API Base URL\n        const API_BASE = \"https://api.arsivtr.xyz\";\n\n        // Param helper: P(name, default, desc, {q: query param, opt: optional, type})\n        const P = (name, def, desc, o = {}) => ({ name, type: o.type || 'string', required: !o.opt, default: def, desc, ...(o.q ? { in: 'query' } : {}) });\n\n        // Endpoint Data Registry\n        const endpoints = [\n            // Hava & Gökyüzü\n            { id: 'hava', title: 'Hava Durumu', category: 'weather', method: 'GET', path: '/hava/{sehir}',\n              description: 'Şehir için anlık hava durumu ve 5 günlük tahmin: sıcaklık, hissedilen, nem, rüzgar, yağış ihtimali.',\n              params: [P('sehir', 'istanbul', 'Şehir adı (Örn: ankara, izmir)'), P('ulke', '', 'Aynı isimli şehirler için ülke kodu (Örn: DE)', { q: 1, opt: 1 })] },\n            { id: 'havakalitesi', title: 'Hava Kalitesi (AQI)', category: 'weather', method: 'GET', path: '/havakalitesi/{sehir}',\n              description: 'Şehrin hava kalitesi indeksi, PM2.5, PM10, ozon ve diğer kirletici değerleri.',\n              params: [P('sehir', 'istanbul', 'Şehir adı'), P('ulke', '', 'Ülke kodu (Örn: TR)', { q: 1, opt: 1 })] },\n            { id: 'gunes', title: 'Gün Doğumu, Batımı & UV', category: 'weather', method: 'GET', path: '/gunes/{sehir}',\n              description: 'Bugün için gün doğumu, gün batımı, gün uzunluğu ve UV indeksi.',\n              params: [P('sehir', 'izmir', 'Şehir adı'), P('ulke', '', 'Ülke kodu (Örn: TR)', { q: 1, opt: 1 })] },\n            { id: 'ay', title: 'Ay Evresi', category: 'weather', method: 'GET', path: '/ay',\n              description: 'Ay evresi, aydınlanma yüzdesi ve sonraki yeni ay / dolunay tarihi.',\n              params: [P('tarih', '', 'YYYY-AA-GG (boş bırakırsanız bugün)', { q: 1, opt: 1 })] },\n\n            // Döviz & Para\n            { id: 'doviz-liste', title: 'Döviz Kurları (Tümü)', category: 'money', method: 'GET', path: '/doviz',\n              description: 'TCMB gösterge kurlarının tamamını TL karşılığıyla listeler.', params: [] },\n            { id: 'doviz', title: 'Tek Döviz Kuru', category: 'money', method: 'GET', path: '/doviz/{kod}',\n              description: 'Seçilen para biriminin TL alış ve satış kuru.',\n              params: [P('kod', 'usd', 'Para birimi kodu (Örn: usd, eur, gbp)')] },\n            { id: 'doviz-cevir', title: 'Döviz Çevirici', category: 'money', method: 'GET', path: '/doviz/{kod}/{hedef}',\n              description: 'Bir para birimini diğerine çevirir. TL için try yazın.',\n              params: [P('kod', 'usd', 'Çevrilecek para birimi'), P('hedef', 'try', 'Hedef para birimi'), P('miktar', '100', 'Miktar (boşsa 1)', { q: 1, opt: 1, type: 'number' })] },\n            { id: 'kdv', title: 'KDV Hesaplama', category: 'money', method: 'GET', path: '/kdv/{tutar}',\n              description: 'KDV hariç tutardan KDV dahil toplamı, veya KDV dahil tutardan matrahı hesaplar.',\n              params: [P('tutar', '1000', 'Tutar (Örn: 1250,50)', { type: 'number' }), P('oran', '20', 'KDV oranı (varsayılan 20)', { q: 1, opt: 1, type: 'number' }), P('dahil', '0', 'Tutar KDV dahilse 1', { q: 1, opt: 1 })] },\n\n            { id: 'kripto-liste', title: 'Kripto Para Fiyatları', category: 'money', method: 'GET', path: '/kripto',\n              description: 'Popüler kripto paraların TL ve USD fiyatı, 24 saatlik değişim.', params: [] },\n            { id: 'kripto', title: 'Tek Kripto Para', category: 'money', method: 'GET', path: '/kripto/{coin}',\n              description: 'Seçilen kripto paranın TL / USD fiyatı ve 24 saatlik değişimi.',\n              params: [P('coin', 'btc', 'Kısa kod (btc, eth, sol, doge...) veya CoinGecko kimliği')] },\n            { id: 'kredi', title: 'Kredi Taksit Hesaplama', category: 'money', method: 'GET', path: '/kredi/{tutar}/{vade}',\n              description: 'Aylık taksit, toplam geri ödeme ve ilk 12 ay ödeme planı. Vergi ve masraflar dahil değildir.',\n              params: [P('tutar', '100000', 'Kredi tutarı', { type: 'number' }), P('vade', '12', 'Vade (ay)', { type: 'integer' }), P('faiz', '3.5', 'Aylık faiz oranı (%)', { q: 1, type: 'number' }), P('tur', 'aylik', 'yillik yazarsanız faiz yıllık kabul edilir', { q: 1, opt: 1 })] },\n            { id: 'mevduat', title: 'Mevduat Getirisi', category: 'money', method: 'GET', path: '/mevduat/{anapara}/{gun}',\n              description: 'Vadeli mevduat için brüt ve net getiri hesaplar.',\n              params: [P('anapara', '100000', 'Yatırılan tutar', { type: 'number' }), P('gun', '32', 'Vade (gün)', { type: 'integer' }), P('faiz', '45', 'Yıllık faiz oranı (%)', { q: 1, type: 'number' }), P('stopaj', '', 'Stopaj oranı (%), boşsa 0', { q: 1, opt: 1, type: 'number' })] },\n\n            { id: 'zekat', title: 'Zekat Hesaplama', category: 'money', method: 'GET', path: '/zekat/{varlik}',\n              description: 'Birikiminizin zekat tutarını hesaplar. Nisap değerini (80,18 gr altının TL karşılığı) siz girersiniz.',\n              params: [P('varlik', '500000', 'Toplam varlık (TL)', { type: 'number' }), P('nisap', '250000', 'Nisap miktarı (TL)', { q: 1, type: 'number' }), P('borc', '', 'Borç (TL), boşsa 0', { q: 1, opt: 1, type: 'number' })] },\n\n            // Günlük Hayat\n            { id: 'deprem', title: 'Son Depremler', category: 'daily', method: 'GET', path: '/deprem',\n              description: 'Son 72 saatteki depremler (AFAD). Büyüklük ve ile göre süzülebilir.',\n              params: [P('min', '3', 'Minimum büyüklük', { q: 1, opt: 1, type: 'number' }), P('limit', '10', 'Kaç kayıt (en fazla 50)', { q: 1, opt: 1, type: 'integer' }), P('il', '', 'İl adına göre süz (Örn: izmir)', { q: 1, opt: 1 })] },\n            { id: 'wiki', title: 'Vikipedi Özeti', category: 'daily', method: 'GET', path: '/wiki/{konu}',\n              description: 'Vikipedi maddesinin kısa özeti, görseli ve bağlantısı.',\n              params: [P('konu', 'Türkiye', 'Madde adı'), P('dil', '', 'Dil kodu (varsayılan tr, örn: en)', { q: 1, opt: 1 })] },\n            { id: 'bugun', title: 'Tarihte Bugün', category: 'daily', method: 'GET', path: '/bugun',\n              description: 'Bugün veya seçilen günde yaşanmış önemli olaylar, doğumlar, ölümler.',\n              params: [P('tarih', '', 'AA-GG (Örn: 10-29, boşsa bugün)', { q: 1, opt: 1 }), P('tur', 'events', 'events, births, deaths veya holidays', { q: 1, opt: 1 }), P('limit', '10', 'Kaç kayıt', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'plaka', title: 'Plaka & Alan Kodu', category: 'daily', method: 'GET', path: '/plaka/{kod}',\n              description: 'Plaka kodundan il, il adından plaka, alan kodundan il bulur.',\n              params: [P('kod', '34', 'Plaka (34), il adı (izmir) veya alan kodu (312)')] },\n            { id: 'burc', title: 'Burç Bulucu', category: 'daily', method: 'GET', path: '/burc/{tarih}',\n              description: 'Doğum tarihine göre burç, element ve tarih aralığı.',\n              params: [P('tarih', '1995-03-25', 'YYYY-AA-GG veya AA-GG')] },\n\n            { id: 'saat', title: 'Dünya Saati', category: 'daily', method: 'GET', path: '/saat/{sehir}',\n              description: 'Dünyanın herhangi bir şehrinde şu an saat kaç? Zaman dilimi de yazabilirsiniz (Europe/London).',\n              params: [P('sehir', 'london', 'Şehir adı veya zaman dilimi')] },\n            { id: 'mesafe', title: 'İki Şehir Arası Mesafe', category: 'daily', method: 'GET', path: '/mesafe/{sehir1}/{sehir2}',\n              description: 'İki şehir arasındaki kuş uçuşu mesafeyi km ve mil olarak verir.',\n              params: [P('sehir1', 'istanbul', 'Başlangıç şehri'), P('sehir2', 'ankara', 'Varış şehri')] },\n            { id: 'tatilkalan', title: 'Sonraki Tatile Kaç Gün Var', category: 'daily', method: 'GET', path: '/tatilkalan',\n              description: 'Bir sonraki resmi tatile kalan gün ve yaklaşan tatillerin listesi.', params: [] },\n            { id: 'hicri', title: 'Hicri Takvim', category: 'daily', method: 'GET', path: '/hicri/{tarih}',\n              description: 'Miladi tarihin hicri takvimdeki karşılığı.',\n              params: [P('tarih', '2026-10-29', 'YYYY-AA-GG')] },\n            { id: 'sozluk', title: 'TDK Sözlük', category: 'daily', method: 'GET', path: '/sozluk/{kelime}',\n              description: 'Türkçe bir kelimenin anlamları ve örnek cümlesi.',\n              params: [P('kelime', 'merhaba', 'Aranacak kelime')] },\n            { id: 'cevir', title: 'Metin Çeviri', category: 'daily', method: 'GET', path: '/cevir',\n              description: 'Kısa metinleri çevirir (en fazla 500 karakter). Kaynak dil boşsa otomatik algılanır.',\n              params: [P('q', 'hello world', 'Çevrilecek metin', { q: 1 }), P('to', 'tr', 'Hedef dil kodu (tr, en, de...)', { q: 1, opt: 1 }), P('from', '', 'Kaynak dil kodu', { q: 1, opt: 1 })] },\n\n            { id: 'tarihyazi', title: 'Tarihi Yazıyla Yaz', category: 'daily', method: 'GET', path: '/tarihyazi/{tarih}',\n              description: 'Rakamla yazılan tarihi yazıya çevirir (dilekçe, sözleşme, senet için).',\n              params: [P('tarih', '2026-10-29', 'YYYY-AA-GG')] },\n            { id: 'telefon', title: 'Telefon Doğrulama', category: 'daily', method: 'GET', path: '/telefon/{numara}',\n              description: 'Türkiye telefon numarasını doğrular, biçimlendirir. Cep ve sabit hat ayrımı, sabit hatta il bilgisi verir.',\n              params: [P('numara', '05321234567', 'Telefon numarası (0, +90, boşluk olabilir)')] },\n            { id: 'dilekce', title: 'Dilekçe Taslağı', category: 'daily', method: 'GET', path: '/dilekce',\n              description: 'Konu, kurum ve bilgilerinizle hazır bir dilekçe taslağı üretir.',\n              params: [P('konu', 'Adres değişikliği', 'Dilekçe konusu', { q: 1 }), P('kurum', '', 'Kurum adı', { q: 1, opt: 1 }), P('ad', '', 'Ad soyad', { q: 1, opt: 1 }), P('adres', '', 'Adres', { q: 1, opt: 1 }), P('aciklama', '', 'Açıklama metni', { q: 1, opt: 1 })] },\n            { id: 'mesaj', title: 'Kutlama Mesajı', category: 'daily', method: 'GET', path: '/mesaj/{tur}',\n              description: 'Bayram, doğum günü, geçmiş olsun gibi hazır mesajlar. Türler: bayram, dogumgunu, gecmisolsun, yeniyil, tebrik, hayirliolsun, gunaydin, iyigeceler.',\n              params: [P('tur', 'bayram', 'Mesaj türü'), P('isim', '', 'Kişinin adı', { q: 1, opt: 1 })] },\n            { id: 'yemek', title: 'Ne Pişirsem?', category: 'daily', method: 'GET', path: '/yemek/{ogun}',\n              description: 'Öğüne ve elinizdeki malzemelere göre yemek önerir. Öğünler: kahvalti, corba, ana, salata, tatli.',\n              params: [P('ogun', 'ana', 'Öğün'), P('malzeme', 'patates', 'Elinizdeki malzemeler (virgülle)', { q: 1, opt: 1 }), P('adet', '3', 'Kaç öneri (en fazla 5)', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'giyim', title: 'Bugün Ne Giysem?', category: 'daily', method: 'GET', path: '/giyim/{sehir}',\n              description: 'Şehrin hava durumuna göre ne giymeniz gerektiğini söyler. Yağmur, rüzgar ve sıcaklığa bakar.',\n              params: [P('sehir', 'istanbul', 'Şehir adı')] },\n            { id: 'varis', title: 'Varış Saati Hesapla', category: 'daily', method: 'GET', path: '/varis/{km}/{hiz}',\n              description: 'Mesafe ve ortalama hızdan yolculuk süresi ve varış saatini hesaplar, molaları ekler.',\n              params: [P('km', '450', 'Mesafe (km)', { type: 'number' }), P('hiz', '90', 'Ortalama hız (km/saat)', { type: 'number' }), P('saat', '', 'Çıkış saati HH:MM (boşsa şu an)', { q: 1, opt: 1 }), P('mola', '15', 'Her 2 saatte mola (dk)', { q: 1, opt: 1, type: 'integer' })] },\n\n            // Hesaplama Araçları\n            { id: 'yas', title: 'Yaş Hesaplama', category: 'calc', method: 'GET', path: '/yas/{tarih}',\n              description: 'Doğum tarihinden yaş, toplam gün, sonraki doğum gününe kalan gün ve burç.',\n              params: [P('tarih', '1995-03-25', 'Doğum tarihi (YYYY-AA-GG)')] },\n            { id: 'tarihfark', title: 'İki Tarih Arası Fark', category: 'calc', method: 'GET', path: '/tarihfark/{baslangic}/{bitis}',\n              description: 'İki tarih arasındaki gün, hafta, ay ve iş günü sayısını verir (resmi tatiller düşülür).',\n              params: [P('baslangic', '2026-01-01', 'Başlangıç tarihi (YYYY-AA-GG)'), P('bitis', '2026-12-31', 'Bitiş tarihi (YYYY-AA-GG)')] },\n            { id: 'bmi', title: 'Vücut Kitle İndeksi', category: 'calc', method: 'GET', path: '/bmi/{boy}/{kilo}',\n              description: 'Boy ve kilodan vücut kitle indeksi ve kategori. Tıbbi tavsiye değildir.',\n              params: [P('boy', '175', 'Boy (cm)', { type: 'number' }), P('kilo', '70', 'Kilo (kg)', { type: 'number' })] },\n            { id: 'birim', title: 'Birim Çevirici', category: 'calc', method: 'GET', path: '/birim/{deger}/{from}/{to}',\n              description: 'Uzunluk, kütle, hacim, hız, alan, veri ve sıcaklık birimlerini çevirir. Birim listesi için /birim.',\n              params: [P('deger', '100', 'Çevrilecek değer', { type: 'number' }), P('from', 'km', 'Kaynak birim (Örn: km, kg, c)'), P('to', 'mi', 'Hedef birim (Örn: mi, lb, f)')] },\n\n            { id: 'indirim', title: 'İndirim Hesaplama', category: 'calc', method: 'GET', path: '/indirim/{fiyat}/{oran}',\n              description: 'İndirim tutarını ve indirimli fiyatı hesaplar.',\n              params: [P('fiyat', '1500', 'Fiyat', { type: 'number' }), P('oran', '25', 'İndirim oranı (%)', { type: 'number' })] },\n            { id: 'yuzde', title: 'Yüzde Hesaplama', category: 'calc', method: 'GET', path: '/yuzde/{a}/{b}',\n              description: \"a'nın yüzde b'si, artış, azalış, a'nın b içindeki yüzdesi ve değişim oranı.\",\n              params: [P('a', '200', 'Birinci sayı', { type: 'number' }), P('b', '15', 'İkinci sayı', { type: 'number' })] },\n            { id: 'bahsis', title: 'Bahşiş & Hesap Bölüşme', category: 'calc', method: 'GET', path: '/bahsis/{hesap}',\n              description: 'Hesaba bahşiş ekler ve kişi başı düşen tutarı bulur.',\n              params: [P('hesap', '850', 'Hesap tutarı', { type: 'number' }), P('yuzde', '10', 'Bahşiş oranı (%)', { q: 1, opt: 1, type: 'number' }), P('kisi', '4', 'Kişi sayısı', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'romen', title: 'Romen Rakamı Çevirici', category: 'calc', method: 'GET', path: '/romen/{sayi}',\n              description: 'Sayıyı romen rakamına veya romen rakamını sayıya çevirir (1-3999).',\n              params: [P('sayi', '1994', 'Sayı (1994) veya romen rakamı (MCMXCIV)')] },\n            { id: 'yaziyla', title: 'Tutarı Yazıya Çevir', category: 'calc', method: 'GET', path: '/yaziyla/{tutar}',\n              description: 'Rakamla yazılan tutarı Türkçe yazıya çevirir. Çek ve senet yazısı için kullanışlıdır.',\n              params: [P('tutar', '1250,50', 'Tutar (Örn: 1250,50)')] },\n\n            { id: 'gno', title: 'Not Ortalaması (GNO)', category: 'calc', method: 'GET', path: '/gno',\n              description: 'Ders notları ve kredilerinden 4\\'lük GNO hesaplar. Harf (AA:3) veya puan (85:3) yazabilirsiniz.',\n              params: [P('dersler', 'AA:3,BB:4,CC:2', 'not:kredi çiftleri, virgülle ayrılır', { q: 1 })] },\n            { id: 'gecmenotu', title: 'Geçme Notu Hesapla', category: 'calc', method: 'GET', path: '/gecmenotu/{vize}',\n              description: 'Vize notunuza göre dersi geçmek için finalden almanız gereken notu bulur.',\n              params: [P('vize', '55', 'Vize notu', { type: 'number' }), P('vizeoran', '40', 'Vize etkisi (%)', { q: 1, opt: 1, type: 'number' }), P('gecme', '60', 'Geçme notu', { q: 1, opt: 1, type: 'number' })] },\n            { id: 'boya', title: 'Boya, Parke, Fayans', category: 'calc', method: 'GET', path: '/boya/{en}/{boy}/{yukseklik}',\n              description: 'Oda ölçüsünden gereken boya litresi, parke paketi ve fayans adedini hesaplar.',\n              params: [P('en', '4', 'Oda eni (m)', { type: 'number' }), P('boy', '5', 'Oda boyu (m)', { type: 'number' }), P('yukseklik', '2.6', 'Tavan yüksekliği (m)', { type: 'number' }), P('kapi', '1', 'Kapı adedi', { q: 1, opt: 1, type: 'integer' }), P('pencere', '1', 'Pencere adedi', { q: 1, opt: 1, type: 'integer' }), P('kat', '2', 'Boya kat sayısı', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'elektrik', title: 'Elektrik Maliyeti', category: 'calc', method: 'GET', path: '/elektrik/{watt}/{saat}',\n              description: 'Bir cihazın aylık elektrik maliyetini hesaplar. Kilowatt saat fiyatını faturanızdan yazın.',\n              params: [P('watt', '1500', 'Cihaz gücü (watt)', { type: 'number' }), P('saat', '3', 'Günlük kullanım (saat)', { type: 'number' }), P('fiyat', '3.2', 'kWh birim fiyatı (TL)', { q: 1, type: 'number' }), P('gun', '30', 'Gün sayısı', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'klima', title: 'Klima BTU Hesapla', category: 'calc', method: 'GET', path: '/klima/{m2}',\n              description: 'Oda büyüklüğüne göre uygun klima kapasitesini (BTU) önerir.',\n              params: [P('m2', '25', 'Oda büyüklüğü (m2)', { type: 'number' }), P('ustkat', '', 'Üst katsa 1', { q: 1, opt: 1 }), P('gunes', '', 'Çok güneş alıyorsa 1', { q: 1, opt: 1 }), P('kisi', '2', 'Odadaki kişi sayısı', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'tuketim', title: 'Yakıt Tüketimi Çevirici', category: 'calc', method: 'GET', path: '/tuketim/{deger}/{from}/{to}',\n              description: 'l/100km, km/l ve mpg (ABD, İngiliz) arasında çevirir. Birimler: l100, kml, mpg, mpguk.',\n              params: [P('deger', '7', 'Değer', { type: 'number' }), P('from', 'l100', 'Kaynak birim'), P('to', 'mpg', 'Hedef birim')] },\n            { id: 'hesapla', title: 'Hesap Makinesi', category: 'calc', method: 'GET', path: '/hesapla',\n              description: 'Matematik ifadesini hesaplar. Parantez, üs (^), sqrt, abs, round, min, max, pi gibi fonksiyonlar desteklenir.',\n              params: [P('ifade', '2*(3+4)^2', 'Matematik ifadesi', { q: 1 })] },\n            { id: 'aktivite', title: 'Yakılan Kalori', category: 'calc', method: 'GET', path: '/aktivite/{tur}/{dakika}',\n              description: 'Spor veya aktivite süresine göre yaklaşık yakılan kaloriyi hesaplar. Liste için /aktivite.',\n              params: [P('tur', 'kosu', 'Aktivite (yuruyus, kosu, bisiklet, yuzme...)'), P('dakika', '30', 'Süre (dakika)', { type: 'number' }), P('kilo', '70', 'Kilonuz (kg)', { q: 1, opt: 1, type: 'number' })] },\n\n            // Eğlence & Karar\n            { id: 'sec', title: 'Karar Verici', category: 'fun', method: 'GET', path: '/sec',\n              description: 'Seçenekler arasından rastgele birini seçer. Ne yesek sorusuna son!',\n              params: [P('liste', 'pizza,kebap,lahmacun,döner', 'Virgülle ayrılmış seçenekler', { q: 1 })] },\n            { id: 'rastgele', title: 'Rastgele Sayı', category: 'fun', method: 'GET', path: '/rastgele/{min}/{max}',\n              description: 'Belirlediğiniz aralıkta rastgele sayı üretir.',\n              params: [P('min', '1', 'En küçük değer', { type: 'integer' }), P('max', '100', 'En büyük değer', { type: 'integer' }), P('adet', '5', 'Kaç sayı (en fazla 100)', { q: 1, opt: 1, type: 'integer' }), P('tekrarsiz', '0', 'Tekrarsız için 1', { q: 1, opt: 1 })] },\n            { id: 'loto', title: 'Loto Kolonu', category: 'fun', method: 'GET', path: '/loto/{oyun}',\n              description: 'Rastgele loto kolonu üretir: sayisal, sanstopu, onnumara, superloto. Eğlence amaçlıdır.',\n              params: [P('oyun', 'sayisal', 'sayisal, sanstopu, onnumara veya superloto'), P('kolon', '1', 'Kaç kolon (en fazla 10)', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'atasozu', title: 'Atasözü', category: 'fun', method: 'GET', path: '/atasozu',\n              description: 'Rastgele bir atasözü ve anlamı. gunluk=1 ile günün atasözünü alın.',\n              params: [P('gunluk', '', 'Günün atasözü için 1', { q: 1, opt: 1 })] },\n\n            // Bot Komutları\n            { id: 'etkilesim', title: 'Etkileşim Komutları (öp, sarıl...)', category: 'bot', method: 'GET', path: '/etkilesim/{eylem}',\n              description: 'Bot komutları için Türkçe ek uyumlu cümle üretir (\"Ahmet, Ayşe\\'yi öptü.\"). Eylemler: op, saril, tokat, elsik, selam, dans, agla, gul, alkis, durt, oksa. gif=1 ile gif linki de gelir.',\n              params: [P('eylem', 'op', 'Eylem'), P('kim', 'Ahmet', 'Eylemi yapan', { q: 1, opt: 1 }), P('kime', 'Ayşe', 'Hedef kişi', { q: 1, opt: 1 }), P('gif', '', 'Gif linki için 1', { q: 1, opt: 1 })] },\n            { id: 'ship', title: 'Ship Uyumluluğu', category: 'bot', method: 'GET', path: '/ship/{isim1}/{isim2}',\n              description: 'İki isim arasında eğlencelik uyum yüzdesi ve ship adı. Aynı çift her zaman aynı sonucu alır.',\n              params: [P('isim1', 'Ahmet', 'Birinci isim'), P('isim2', 'Ayşe', 'İkinci isim')] },\n            { id: '8top', title: 'Sihirli 8 Top', category: 'bot', method: 'GET', path: '/8top',\n              description: 'Evet, hayır ya da belki. Sorunuzu sorun, top cevaplasın.',\n              params: [P('soru', '', 'Sorunuz', { q: 1, opt: 1 })] },\n            { id: 'dogruluk-cesaret', title: 'Doğruluk mu Cesaret mi', category: 'bot', method: 'GET', path: '/dogruluk-cesaret/{tur}',\n              description: 'Doğruluk sorusu veya cesaret görevi verir.',\n              params: [P('tur', 'cesaret', 'dogruluk veya cesaret'), P('seviye', '', 'hafif, orta veya eglenceli', { q: 1, opt: 1 })] },\n            { id: 'fal', title: 'Günlük Fal', category: 'bot', method: 'GET', path: '/fal/{burc}',\n              description: 'Burca göre eğlencelik günlük fal. Aynı gün aynı burç aynı sonucu alır. Burç yazmazsanız kahve falı gelir.',\n              params: [P('burc', 'koc', 'Burç adı (koc, boga, ikizler...)')] },\n            { id: 'iltifat', title: 'Rastgele İltifat', category: 'bot', method: 'GET', path: '/iltifat',\n              description: 'Birine iltifat eder. İsim verirseniz kişiselleştirir.',\n              params: [P('isim', '', 'Kişinin adı', { q: 1, opt: 1 })] },\n            { id: 'espri', title: 'Espri ve Fıkra', category: 'bot', method: 'GET', path: '/espri/{tur}',\n              description: 'Kısa espri veya Nasreddin Hoca fıkrası.',\n              params: [P('tur', 'espri', 'espri veya fikra')] },\n            { id: 'bilmece', title: 'Bilmece', category: 'bot', method: 'GET', path: '/bilmece',\n              description: 'Rastgele bilmece ve cevabı. gizle=1 ile cevap saklanır, sadece ipucu gelir.',\n              params: [P('gizle', '', 'Cevabı gizlemek için 1', { q: 1, opt: 1 })] },\n            { id: 'quiz', title: 'Bilgi Yarışması', category: 'bot', method: 'GET', path: '/quiz/{kategori}',\n              description: 'Çoktan seçmeli soru. Kategoriler: cografya, tarih, genel. gizle=1 ile doğru cevap saklanır.',\n              params: [P('kategori', 'genel', 'Kategori'), P('gizle', '', 'Cevabı gizlemek için 1', { q: 1, opt: 1 })] },\n            { id: 'adamasmaca', title: 'Adam Asmaca Kelimesi', category: 'bot', method: 'GET', path: '/adamasmaca/{zorluk}',\n              description: 'Kelime, ipucu ve maske verir. Zorluk: kolay, orta, zor.',\n              params: [P('zorluk', 'orta', 'Zorluk seviyesi'), P('gizle', '', 'Kelimeyi gizlemek için 1', { q: 1, opt: 1 })] },\n            { id: 'wordle', title: 'Wordle (Kelime Oyunu)', category: 'bot', method: 'GET', path: '/wordle',\n              description: '5 harfli kelime verir veya tahmini değerlendirir (dogru, var, yok). gunluk=1 ile günün kelimesi sabit kalır.',\n              params: [P('gunluk', '1', 'Günün kelimesi için 1', { q: 1, opt: 1 }), P('tahmin', 'kalem', '5 harfli tahmin', { q: 1, opt: 1 })] },\n            { id: 'tkm', title: 'Taş Kağıt Makas', category: 'bot', method: 'GET', path: '/tkm/{hamle}',\n              description: 'Botla taş kağıt makas oynayın.',\n              params: [P('hamle', 'tas', 'tas, kagit veya makas')] },\n            { id: 'kart', title: 'Kart Çek / Poker', category: 'bot', method: 'GET', path: '/kart',\n              description: '52\\'lik desteden kart çeker. oyun=poker ile 5 kart dağıtıp elin adını söyler.',\n              params: [P('adet', '5', 'Kaç kart', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'takmaad', title: 'Takma Ad Üretici', category: 'bot', method: 'GET', path: '/takmaad/{tur}',\n              description: 'Oyuncu, klan veya sunucu için isim önerir.',\n              params: [P('tur', 'oyuncu', 'oyuncu, klan veya sunucu'), P('adet', '5', 'Kaç isim (en fazla 20)', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'karakter', title: 'RPG Karakteri', category: 'bot', method: 'GET', path: '/karakter',\n              description: 'Rastgele irk, sınıf, silah ve özelliklere sahip bir rol yapma karakteri üretir.', params: [] },\n            { id: 'hediye', title: 'Hediye Önerisi', category: 'bot', method: 'GET', path: '/hediye/{kisi}',\n              description: 'Kişiye ve bütçeye göre hediye fikri. Kişiler: anne, baba, sevgili, arkadas, cocuk, ofis.',\n              params: [P('kisi', 'anne', 'Kişi'), P('butce', '', 'uygun, orta veya ozel', { q: 1, opt: 1 })] },\n\n            // Yazılımcı Araçları\n            { id: 'sahte', title: 'Sahte Kişi Verisi', category: 'dev', method: 'GET', path: '/sahte/kisi',\n              description: 'Test için sahte kişi üretir: geçerli TCKN, IBAN, telefon, e-posta, adres. Gerçek kişilere ait değildir.',\n              params: [P('adet', '3', 'Kaç kişi (en fazla 20)', { q: 1, opt: 1, type: 'integer' }), P('cinsiyet', '', 'erkek veya kadin', { q: 1, opt: 1 })] },\n            { id: 'cron', title: 'Cron Açıklayıcı', category: 'dev', method: 'GET', path: '/cron',\n              description: 'Cron ifadesini Türkçe açıklar ve sonraki çalışma zamanlarını Türkiye saatiyle listeler.',\n              params: [P('ifade', '*/15 9-17 * * 1-5', 'Cron ifadesi (5 alan)', { q: 1 }), P('adet', '5', 'Kaç çalışma zamanı', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'durumkodu', title: 'HTTP Durum Kodu', category: 'dev', method: 'GET', path: '/durumkodu/{kod}',\n              description: 'HTTP durum kodunun Türkçe açıklaması. Kod yazmazsanız tüm liste gelir.',\n              params: [P('kod', '404', 'Durum kodu', { type: 'integer' })] },\n            { id: 'cidr', title: 'CIDR / Subnet Hesapla', category: 'dev', method: 'GET', path: '/cidr/{ag}',\n              description: 'IPv4 ağ bloğunun maske, yayın adresi, kullanılabilir IP aralığı ve host sayısını hesaplar.',\n              params: [P('ag', '192.168.1.0/24', 'Ağ (Örn: 10.0.0.0/16)')] },\n            { id: 'ua', title: 'User-Agent Çözümleyici', category: 'dev', method: 'GET', path: '/ua',\n              description: 'User-Agent metninden tarayıcı, işletim sistemi, cihaz türü ve bot bilgisini çıkarır. Boş bırakırsanız kendi tarayıcınızı çözer.',\n              params: [P('q', '', 'User-Agent metni (boşsa sizinki)', { q: 1, opt: 1 })] },\n            { id: 'lorem', title: 'Türkçe Lorem Ipsum', category: 'dev', method: 'GET', path: '/lorem/{paragraf}',\n              description: 'Tasarım ve test için Türkçe sözcüklerden oluşan örnek metin üretir.',\n              params: [P('paragraf', '3', 'Paragraf sayısı (en fazla 10)', { type: 'integer' }), P('cumle', '4', 'Paragraf başına cümle', { q: 1, opt: 1, type: 'integer' })] },\n            { id: 'json', title: 'JSON Doğrula / Güzelleştir', category: 'dev', method: 'GET', path: '/json',\n              description: 'JSON metnini doğrular, biçimlendirir veya küçültür. Hata varsa nedenini söyler.',\n              params: [P('q', '{\"ad\":\"Ali\",\"yas\":30}', 'JSON metni (en fazla 5000 karakter)', { q: 1 }), P('islem', 'format', 'format, minify veya dogrula', { q: 1, opt: 1 })] },\n            { id: 'regex', title: 'Regex Test', category: 'dev', method: 'GET', path: '/regex',\n              description: 'Düzenli ifadeyi bir metinde dener, eşleşmeleri ve grupları gösterir.',\n              params: [P('desen', '(\\\\d+)-(\\\\d+)', 'Regex deseni', { q: 1 }), P('metin', '10-20 ve 30-40', 'Test metni', { q: 1 }), P('bayrak', 'g', 'Bayraklar (g, i, m, s...)', { q: 1, opt: 1 })] },\n            { id: 'metinstil', title: 'Metin Araçları', category: 'dev', method: 'GET', path: '/metinstil/{stil}',\n              description: 'Türkçe büyük/küçük harf, ters, slug, mors, binary, hex, leet, ASCII, kelime sayacı ve daha fazlası. Liste için /metinstil.',\n              params: [P('stil', 'buyuk', 'Stil (buyuk, kucuk, ters, slug, mors, say...)'), P('q', 'istanbul ışık', 'Metin', { q: 1 })] },\n            { id: 'epostakontrol', title: 'E-posta Kontrol', category: 'dev', method: 'GET', path: '/epostakontrol/{adres}',\n              description: 'E-posta biçimini, MX kaydını ve tek kullanımlık alan adı olup olmadığını kontrol eder. Yazım hatası önerir.',\n              params: [P('adres', 'ornek@gmail.com', 'E-posta adresi')] },\n\n\n\n            // Domain & Network\n            {\n                id: 'whois',\n                title: 'Whois Sorgulama',\n                category: 'network',\n                method: 'GET',\n                path: '/whois/{domain}',\n                description: 'Belirtilen domain adresi için kayıtlı registrar, registrar tarihi, NS ve Whois detaylarını döndürür.',\n                params: [{ name: 'domain', type: 'string', required: true, default: 'example.com', desc: 'Sorgulanacak alan adı' }]\n            },\n            {\n                id: 'dns',\n                title: 'DNS Kayıtları',\n                category: 'network',\n                method: 'GET',\n                path: '/dns/{domain}',\n                description: 'Domain adresi için A, AAAA, MX, TXT, NS ve CNAME kayıtlarını listeler.',\n                params: [{ name: 'domain', type: 'string', required: true, default: 'google.com', desc: 'DNS kayıtları istenen alan adı' }]\n            },\n            {\n                id: 'available',\n                title: 'Domain Müsaitlik Kontrolü',\n                category: 'network',\n                method: 'GET',\n                path: '/available/{domain}',\n                description: 'Domain adresinin kayıt edilmeye müsait olup olmadığını kontrol eder.',\n                params: [{ name: 'domain', type: 'string', required: true, default: 'arsivtr-test-domain-123.com', desc: 'Kontrol edilecek alan adı' }]\n            },\n            {\n                id: 'ssl',\n                title: 'SSL Sertifika Analizi',\n                category: 'network',\n                method: 'GET',\n                path: '/ssl/{domain}',\n                description: 'Domain üzerindeki SSL sertifikasının geçerlilik tarihini, yayıncısını ve durumunu döndürür.',\n                params: [{ name: 'domain', type: 'string', required: true, default: 'github.com', desc: 'SSL analizi yapılacak alan adı' }]\n            },\n            {\n                id: 'headers',\n                title: 'HTTP Response Headers',\n                category: 'network',\n                method: 'GET',\n                path: '/headers/{domain}',\n                description: 'Hedef alan adından dönen sunucu header yanıtlarını detaylıca inceler.',\n                params: [{ name: 'domain', type: 'string', required: true, default: 'cloudflare.com', desc: 'Header verisi alınacak site' }]\n            },\n            {\n                id: 'expand',\n                title: 'Kısaltılmış URL Genişletici',\n                category: 'network',\n                method: 'GET',\n                path: '/expand/{url}',\n                description: 'Kısaltılmış bağlantıların arkasındaki nihai hedef URL adresini çözer.',\n                params: [{ name: 'url', type: 'string', required: true, default: 'https://tinyurl.com/example', desc: 'Çözümlenecek kısa bağlantı (URL Encoded)' }]\n            },\n            {\n                id: 'ip',\n                title: 'IP Coğrafi Konum & Bilgi',\n                category: 'network',\n                method: 'GET',\n                path: '/ip/{ip}',\n                description: 'IP adresinin ülke, şehir, koordinat, ISP ve lokasyon bilgilerini getirir.',\n                params: [{ name: 'ip', type: 'string', required: true, default: '8.8.8.8', desc: 'Sorgulanacak IPv4 veya IPv6 adresi' }]\n            },\n            {\n                id: 'asn',\n                title: 'ASN Detay Sorgulama',\n                category: 'network',\n                method: 'GET',\n                path: '/asn/{ip}',\n                description: 'IP adresinin bağlı olduğu Otonom Sistem Numarası (ASN) bilgilerini sunar.',\n                params: [{ name: 'ip', type: 'string', required: true, default: '1.1.1.1', desc: 'Otonom sistem detayı için IP adresi' }]\n            },\n            {\n                id: 'blacklist',\n                title: 'IP Karaliste (Blacklist) Kontrolü',\n                category: 'network',\n                method: 'GET',\n                path: '/blacklist/{ip}',\n                description: 'IP adresinin popüler spam ve güvenlik karalistelerinde olup olmadığını sorgular.',\n                params: [{ name: 'ip', type: 'string', required: true, default: '1.1.1.1', desc: 'Kontrol edilecek IP adresi' }]\n            },\n            {\n                id: 'myip',\n                title: 'Kendi IP Adresini Öğren',\n                category: 'network',\n                method: 'GET',\n                path: '/myip',\n                description: 'İstekte bulunan istemcinin dış IP adresini ve istemci bilgilerini döndürür.',\n                params: []\n            },\n\n            // Verification\n            {\n                id: 'mail-verify',\n                title: 'E-Posta Adresi Doğrulama',\n                category: 'verification',\n                method: 'GET',\n                path: '/mail/{eposta}',\n                description: 'E-posta adresinin biçimsel geçerliliğini, MX kayıtlarını ve kullanılıp kullanılamadığını doğrular.',\n                params: [{ name: 'eposta', type: 'string', required: true, default: 'test@gmail.com', desc: 'Kontrol edilecek e-posta adresi' }]\n            },\n            {\n                id: 'iban-verify',\n                title: 'IBAN Doğrulama',\n                category: 'verification',\n                method: 'GET',\n                path: '/iban/{iban}',\n                description: 'TR ve uluslararası IBAN numaralarının algoritma kontrollerini yapar ve banka kodunu çözer.',\n                params: [{ name: 'iban', type: 'string', required: true, default: 'TR330006100511123456789012', desc: 'Doğrulanacak IBAN numarası' }]\n            },\n            {\n                id: 'tckn-verify',\n                title: 'TCKN Algoritma Kontrolü',\n                category: 'verification',\n                method: 'GET',\n                path: '/tckn/{no}',\n                description: 'Türkiye Cumhuriyeti Kimlik Numarasının matematiksel doğrulama algoritmasını kontrol eder.',\n                params: [{ name: 'no', type: 'string', required: true, default: '10000000146', desc: '11 haneli T.C. Kimlik Numarası' }]\n            },\n            {\n                id: 'vkn-verify',\n                title: 'VKN Doğrulama',\n                category: 'verification',\n                method: 'GET',\n                path: '/vkn/{no}',\n                description: '10 haneli Vergi Kimlik Numarasının (VKN) matematiksel doğrulamasını gerçekleştirir.',\n                params: [{ name: 'no', type: 'string', required: true, default: '1234567890', desc: '10 haneli Vergi Kimlik Numarası' }]\n            },\n\n            // Turkey Data\n            {\n                id: 'tatil-year',\n                title: 'Yıllık Resmi Tatiller',\n                category: 'turkey',\n                method: 'GET',\n                path: '/tatil/{yil}',\n                description: 'Türkiye için ilgili yıldaki tüm resmi ve dini tatil günlerinin listesini getirir.',\n                params: [{ name: 'yil', type: 'integer', required: true, default: '2026', desc: 'Sorgulanacak yıl (Örn: 2026)' }]\n            },\n            {\n                id: 'tatil-date',\n                title: 'Tarih Resmi Tatil mi?',\n                category: 'turkey',\n                method: 'GET',\n                path: '/tatil/{yyyy-aa-gg}',\n                description: 'Belirtilen belirli bir günün resmi tatil olup olmadığını sorgular.',\n                params: [{ name: 'yyyy-aa-gg', type: 'string', required: true, default: '2026-10-29', desc: 'YYYY-AA-GG formatında tarih' }]\n            },\n            {\n                id: 'namaz',\n                title: 'Namaz Vakitleri',\n                category: 'turkey',\n                method: 'GET',\n                path: '/namaz/{sehir}',\n                description: 'Türkiye şehirleri için günlük ezan ve namaz vakitlerini getirir.',\n                params: [{ name: 'sehir', type: 'string', required: true, default: 'istanbul', desc: 'İl adı (Örn: istanbul, ankara)' }, { name: 'ulke', in: 'query', type: 'string', required: false, default: '', desc: 'Başka ülke için (Örn: Germany)' }]\n            },\n\n            // Tools & Cryptography\n            {\n                id: 'hash',\n                title: 'Metin Hash Oluşturucu',\n                category: 'tools',\n                method: 'GET',\n                path: '/hash/{metin}',\n                description: 'Girilmiş metin için MD5, SHA1, SHA256 ve SHA512 hash özetlerini üretir.',\n                params: [{ name: 'metin', type: 'string', required: true, default: 'arsivtr', desc: 'Hashlenecek içerik' }]\n            },\n            {\n                id: 'base64-encode',\n                title: 'Base64 Encode',\n                category: 'tools',\n                method: 'GET',\n                path: '/base64/encode/{metin}',\n                description: 'Düz metni Base64 formatına dönüştürür.',\n                params: [{ name: 'metin', type: 'string', required: true, default: 'Merhaba Dunya', desc: 'Dönüştürülecek metin' }]\n            },\n            {\n                id: 'base64-decode',\n                title: 'Base64 Decode',\n                category: 'tools',\n                method: 'GET',\n                path: '/base64/decode/{base64}',\n                description: 'Base64 ile kodlanmış veriyi orijinal metne çevirir.',\n                params: [{ name: 'base64', type: 'string', required: true, default: 'TWVyaGFiYSBEdW55YQ==', desc: 'Çözülecek Base64 dizesi' }]\n            },\n            {\n                id: 'url-encode',\n                title: 'URL Encode',\n                category: 'tools',\n                method: 'GET',\n                path: '/url/encode/{metin}',\n                description: 'Metni güvenli URL formatında kodlar.',\n                params: [{ name: 'metin', type: 'string', required: true, default: 'hello world & key=value', desc: 'Kodlanacak metin' }]\n            },\n            {\n                id: 'url-decode',\n                title: 'URL Decode',\n                category: 'tools',\n                method: 'GET',\n                path: '/url/decode/{metin}',\n                description: 'URL encode yapılmış metni orijinal haline çözer.',\n                params: [{ name: 'metin', type: 'string', required: true, default: 'hello%20world%20%26%20key%3Dvalue', desc: 'Çözümlenecek metin' }]\n            },\n            {\n                id: 'jwt',\n                title: 'JWT Token Çözücü',\n                category: 'tools',\n                method: 'GET',\n                path: '/jwt/{token}',\n                description: 'JSON Web Token (JWT) içeriğindeki header ve payload verilerini çözümler.',\n                params: [{ name: 'token', type: 'string', required: true, default: 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.e30.t-IDc25OHYBRd5gU15W5uE-hMCHM0L_Z34U6_v1oXrg', desc: 'JWT token dizesi' }]\n            },\n            {\n                id: 'uuid',\n                title: 'UUID v4 Üretici',\n                category: 'tools',\n                method: 'GET',\n                path: '/uuid',\n                description: 'Benzersiz rastgele bir UUID v4 dizesi üretir.',\n                params: [{ name: 'adet', in: 'query', type: 'integer', required: false, default: '1', desc: 'Kaç UUID üretilecek' }, { name: 'v', in: 'query', type: 'integer', required: false, default: '4', desc: 'UUID sürümü (4 veya 7)' }]\n            },\n            {\n                id: 'password',\n                title: 'Rastgele Güvenli Şifre',\n                category: 'tools',\n                method: 'GET',\n                path: '/password',\n                description: 'Kriptografik olarak güvenli, karmaşık rastgele parola oluşturur.',\n                params: [{ name: 'uzunluk', in: 'query', type: 'integer', required: false, default: '20', desc: 'Parola uzunluğu' }, { name: 'adet', in: 'query', type: 'integer', required: false, default: '1', desc: 'Kaç parola üretilecek' }]\n            },\n            {\n                id: 'qr',\n                title: 'Hızlı QR Kodu Servisi',\n                category: 'tools',\n                method: 'GET',\n                path: '/qr/{metin}',\n                description: 'Girilmiş metin veya URL için dinamik QR kod görseli veya verisi üretir.',\n                params: [{ name: 'metin', type: 'string', required: true, default: 'https://api.arsivtr.xyz', desc: 'QR koda dönüştürülecek veri' }]\n            },\n            {\n                id: 'qrcode-custom',\n                title: 'Özelleştirilmiş QR Kod',\n                category: 'tools',\n                method: 'GET',\n                path: '/qrcode/custom',\n                description: 'Boyut, renk ve hata tolerans parametreleri ile özel QR kodlar üretir.',\n                params: [{ name: 'text', in: 'query', type: 'string', required: true, default: 'https://api.arsivtr.xyz', desc: 'QR koda yazılacak metin / URL' }, { name: 'logo', in: 'query', type: 'string', required: false, default: 'APITR', desc: 'Ortadaki logo: HTTPS görsel linki veya kısa yazı (max 8 karakter)' }]\n            },\n            {\n                id: 'color',\n                title: 'Renk Paleti & HEX Çözücü',\n                category: 'tools',\n                method: 'GET',\n                path: '/color/{hex}',\n                description: 'HEX renk kodunun RGB, HSL ve yakın renk detaylarını sağlar.',\n                params: [{ name: 'hex', type: 'string', required: true, default: '6366f1', desc: '6 haneli HEX renk kodu' }]\n            },\n            {\n                id: 'roll',\n                title: 'Zar Atma (Dice Roll)',\n                category: 'tools',\n                method: 'GET',\n                path: '/roll/{NdM}',\n                description: 'Masaüstü rol yapma oyunları için standart zar formatında (Örn: 2d6, 1d20) rastgele zar atar.',\n                params: [{ name: 'NdM', type: 'string', required: true, default: '2d6', desc: 'Zar formatı (Örn: 1d6, 2d20)' }]\n            },\n            {\n                id: 'flip',\n                title: 'Yazı Tura At',\n                category: 'tools',\n                method: 'GET',\n                path: '/flip',\n                description: 'Rastgele Yazı (Heads) veya Tura (Tails) sonucu döndürür.',\n                params: [{ name: 'count', in: 'query', type: 'integer', required: false, default: '3', desc: 'Kaç kez atılacağı (1-100)' }]\n            },\n            {\n                id: 'minecraft',\n                title: 'Minecraft Sunucu Durumu',\n                category: 'tools',\n                method: 'GET',\n                path: '/minecraft/{sunucu}',\n                description: 'Minecraft sunucusunun aktif oyuncu sayısını, motd mesajını ve versiyonunu getirir.',\n                params: [{ name: 'sunucu', type: 'string', required: true, default: 'hypixel.net', desc: 'Minecraft sunucu IP veya domain adresi' }]\n            },\n            {\n                id: 'screenshot',\n                title: 'Web Sitesi Ekran Görüntüsü',\n                category: 'tools',\n                method: 'GET',\n                path: '/screenshot',\n                description: 'Verilen web adresinin anlık ekran görüntüsünü alır.',\n                params: [{ name: 'url', in: 'query', type: 'string', required: true, default: 'https://github.com', desc: 'Ekran görüntüsü alınacak HTTPS adres' }]\n            },\n            {\n                id: 'lyrics',\n                title: 'Şarkı Sözü Arama',\n                category: 'tools',\n                method: 'GET',\n                path: '/lyrics',\n                description: 'Şarkı adı ve sanatçı bilgisine göre şarkı sözlerini getirir.',\n                params: [{ name: 'q', in: 'query', type: 'string', required: true, default: 'Tarkan Şımarık', desc: 'Şarkı veya sanatçı adı' }]\n            },\n\n            // Temp Mail\n            {\n                id: 'tempmail-new',\n                title: 'Yeni Geçici E-Posta Oluştur',\n                category: 'tempmail',\n                method: 'POST',\n                path: '/tempmail/new',\n                description: 'Anında kullanıma hazır rastgele geçici bir e-posta adresi oluşturur. POST olduğu için buton yeni sekmede form ile POST gönderir.',\n                params: []\n            },\n            {\n                id: 'tempmail-inbox',\n                title: 'Geçici Kutuyu (Inbox) Kontrol Et',\n                category: 'tempmail',\n                method: 'GET',\n                path: '/tempmail/inbox/{id}',\n                description: 'Oluşturulmuş geçici e-posta adresine gelen e-postaları ve gelen içerikleri okur.',\n                params: [{ name: 'id', type: 'string', required: true, default: 'test-user-id', desc: 'Geçici e-posta kütüphane ID adresi' }]\n            }\n        ];\n\n        const categoryLabels = { bot: 'Bot Komutları', dev: 'Yazılımcı', fun: 'Eğlence & Karar', weather: 'Hava & Gökyüzü', money: 'Döviz & Para', daily: 'Günlük Hayat', calc: 'Hesaplama', network: 'Domain & Network', verification: 'Doğrulama', turkey: 'Türkiye', tools: 'Araçlar', tempmail: 'Temp Mail' };\n\n        // 'YENİ' rozeti ve 'Yeni Eklenenler' filtresi. Yeni eklenen endpoint'in id'sini buraya yazmanız yeterli.\n        const NEW_IDS = new Set(['zekat', 'tarihyazi', 'telefon', 'dilekce', 'mesaj', 'yemek', 'giyim', 'varis', 'gno', 'gecmenotu', 'boya', 'elektrik', 'klima', 'tuketim', 'hesapla', 'aktivite', 'etkilesim', 'ship', '8top', 'dogruluk-cesaret', 'fal', 'iltifat', 'espri', 'bilmece', 'quiz', 'adamasmaca', 'wordle', 'tkm', 'kart', 'takmaad', 'karakter', 'hediye', 'sahte', 'cron', 'durumkodu', 'cidr', 'ua', 'lorem', 'json', 'regex', 'metinstil', 'epostakontrol']);\n        endpoints.forEach(ep => { ep.isNew = NEW_IDS.has(ep.id); });\n\n        // State Management\n        let activeCategory = 'all';\n\n        // Render Endpoints Function\n        function renderEndpoints() {\n            const container = document.getElementById('endpoints-list');\n            const searchQuery = (document.getElementById('endpoint-search').value || document.getElementById('endpoint-search-mobile').value || '').toLowerCase();\n            \n            container.innerHTML = '';\n\n            const filtered = endpoints.filter(ep => {\n                const matchesCat = activeCategory === 'all' || (activeCategory === 'new' ? ep.isNew : ep.category === activeCategory);\n                const matchesSearch = ep.title.toLowerCase().includes(searchQuery) || \n                                      ep.path.toLowerCase().includes(searchQuery) ||\n                                      ep.description.toLowerCase().includes(searchQuery);\n                return matchesCat && matchesSearch;\n            });\n\n            if (filtered.length === 0) {\n                container.innerHTML = `\n                    <div class=\"p-12 text-center rounded-3xl border border-gray-200 dark:border-darkborder bg-white dark:bg-darkcard\">\n                        <svg class=\"w-12 h-12 mx-auto text-gray-400 mb-3\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M9.172 9.172a4 4 0 015.656 0M9 10h.01M15 10h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z\"/></svg>\n                        <h3 class=\"text-base font-semibold text-gray-800 dark:text-gray-200\">Endpoint Bulunamadı</h3>\n                        <p class=\"text-xs text-gray-500 mt-1\">Arama terimlerinizi veya filtrelerinizi değiştirmeyi deneyin.</p>\n                    </div>\n                `;\n                return;\n            }\n\n            filtered.forEach(ep => {\n                const methodColor = ep.method === 'GET' \n                    ? 'bg-gray-100 text-gray-800 dark:bg-white/10 dark:text-gray-200 border-gray-300 dark:border-white/20' \n                    : 'bg-black text-white dark:bg-white dark:text-black border-black dark:border-white';\n\n                const cardHtml = `\n                    <div id=\"card-${ep.id}\" class=\"endpoint-card ${ep.isNew ? 'border-l-4 border-l-emerald-500' : ''} rounded-2xl border border-gray-200/80 dark:border-darkborder bg-white dark:bg-darkcard overflow-hidden shadow-sm transition-all duration-200\">\n                        <!-- Card Header Accordion -->\n                        <button onclick=\"toggleCard('${ep.id}')\" class=\"w-full p-4 sm:p-5 flex items-center justify-between text-left hover:bg-gray-50/50 dark:hover:bg-gray-800/30 transition\">\n                            <div class=\"flex items-center gap-3 sm:gap-4 min-w-0\">\n                                <span class=\"px-2.5 py-1 text-xs font-bold rounded-lg border ${methodColor}\">${ep.method}</span>\n                                <div class=\"min-w-0\">\n                                    <div class=\"flex items-center gap-2\">\n                                        <h3 class=\"font-semibold text-gray-900 dark:text-gray-100 text-sm sm:text-base truncate\">${ep.title}</h3>\n                                    </div>\n                                    <p class=\"text-xs font-mono text-gray-500 dark:text-gray-400 truncate mt-0.5\">${ep.path}</p>\n                                </div>\n                            </div>\n                            <div class=\"flex items-center gap-3 shrink-0 ml-2\">\n                                ${ep.isNew ? '<span class=\"shrink-0 text-[10px] font-extrabold tracking-wider px-2 py-1 rounded-md bg-emerald-500 text-white shadow-sm\">YENİ</span>' : ''}\n                                <span class=\"hidden sm:inline-block text-xs font-medium px-2.5 py-1 rounded-full bg-gray-100 dark:bg-gray-800 text-gray-500 dark:text-gray-400 \">${categoryLabels[ep.category] || ep.category}</span>\n                                <svg id=\"chevron-${ep.id}\" class=\"w-5 h-5 text-gray-400 transition-transform duration-200\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M19 9l-7 7-7-7\"/></svg>\n                            </div>\n                        </button>\n\n                        <!-- Card Expanded Content -->\n                        <div id=\"content-${ep.id}\" class=\"hidden border-t border-gray-100 dark:border-gray-800/60 p-5 sm:p-6 space-y-6 bg-gray-50/30 dark:bg-gray-900/20\">\n                            <p class=\"text-xs sm:text-sm text-gray-600 dark:text-gray-300 leading-relaxed\">${ep.description}</p>\n\n                            <!-- Parameters Form Section -->\n                            ${ep.params.length > 0 ? `\n                                <div class=\"space-y-3\">\n                                    <h4 class=\"text-xs font-bold uppercase tracking-wider text-gray-400\">Parametreler</h4>\n                                    <div class=\"space-y-2\">\n                                        ${ep.params.map(p => `\n                                            <div class=\"flex flex-col sm:flex-row sm:items-center justify-between gap-2 p-3 rounded-xl bg-white dark:bg-gray-900 border border-gray-200/70 dark:border-gray-800\">\n                                                <div class=\"space-y-0.5\">\n                                                    <div class=\"flex items-center gap-2\">\n                                                        <span class=\"text-xs font-mono font-semibold text-gray-800 dark:text-gray-200\">${p.name}</span>\n                                                        <span class=\"text-[10px] px-1.5 py-0.5 rounded bg-gray-100 dark:bg-gray-800 text-gray-500 font-mono\">${p.type}${p.in === 'query' ? ' · query' : ''}</span>\n                                                        ${p.required ? '<span class=\"text-[10px] text-red-500 font-medium\">*gerekli</span>' : '<span class=\"text-[10px] text-gray-400 font-medium\">opsiyonel</span>'}\n                                                    </div>\n                                                    <p class=\"text-xs text-gray-400\">${p.desc}</p>\n                                                </div>\n                                                <input type=\"text\" id=\"input-${ep.id}-${p.name}\" value=\"${String(p.default).replace(/&/g, '&amp;').replace(/\"/g, '&quot;')}\" oninput=\"updateSnippet('${ep.id}')\" class=\"w-full sm:w-64 px-3 py-1.5 text-xs font-mono rounded-lg border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-800 focus:ring-2 focus:ring-neutral-500 focus:outline-none\">\n                                            </div>\n                                        `).join('')}\n                                    </div>\n                                </div>\n                            ` : ''}\n\n                            <!-- Code Generator Tabs & Execute Button -->\n                            <div class=\"space-y-3\">\n                                <div class=\"flex flex-col sm:flex-row sm:items-center justify-between gap-3\">\n                                    <div class=\"flex items-center gap-1 bg-gray-200/60 dark:bg-gray-800/80 p-1 rounded-xl w-fit\">\n                                        <button onclick=\"setTab('${ep.id}', 'curl')\" id=\"tab-${ep.id}-curl\" class=\"tab-btn active px-3 py-1 rounded-lg text-xs font-medium transition bg-white dark:bg-gray-900 text-gray-900 dark:text-white shadow-sm\">cURL</button>\n                                        <button onclick=\"setTab('${ep.id}', 'fetch')\" id=\"tab-${ep.id}-fetch\" class=\"tab-btn px-3 py-1 rounded-lg text-xs font-medium text-gray-500 hover:text-gray-900 dark:hover:text-white transition\">Fetch JS</button>\n                                        <button onclick=\"setTab('${ep.id}', 'python')\" id=\"tab-${ep.id}-python\" class=\"tab-btn px-3 py-1 rounded-lg text-xs font-medium text-gray-500 hover:text-gray-900 dark:hover:text-white transition\">Python</button>\n                                        <button onclick=\"setTab('${ep.id}', 'node')\" id=\"tab-${ep.id}-node\" class=\"tab-btn px-3 py-1 rounded-lg text-xs font-medium text-gray-500 hover:text-gray-900 dark:hover:text-white transition\">Node.js</button>\n                                    </div>\n                                    <button onclick=\"executeRequest('${ep.id}')\" class=\"flex items-center justify-center gap-2 px-4 py-2 rounded-xl bg-black hover:bg-neutral-800 text-white dark:bg-white dark:hover:bg-neutral-200 dark:text-black font-medium text-xs transition shadow-md active:scale-95\">\n                                        <svg class=\"w-4 h-4\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M10 6H6a2 2 0 00-2 2v10a2 2 0 002 2h10a2 2 0 002-2v-4M14 4h6m0 0v6m0-6L10 14\"/></svg>\n                                        <span>Linki Aç</span>\n                                    </button>\n                                </div>\n\n                                <!-- Code Output Display -->\n                                <div class=\"relative rounded-xl overflow-hidden bg-gray-900 border border-gray-800 text-gray-100\">\n                                    <button onclick=\"copyCodeSnippet('${ep.id}')\" class=\"absolute right-3 top-3 p-1.5 rounded-lg bg-gray-800 hover:bg-gray-700 text-gray-300 transition\" title=\"Kod Kopyala\">\n                                        <svg class=\"w-4 h-4\" fill=\"none\" stroke=\"currentColor\" viewBox=\"0 0 24 24\"><path stroke-linecap=\"round\" stroke-linejoin=\"round\" stroke-width=\"2\" d=\"M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z\"/></svg>\n                                    </button>\n                                    <pre class=\"p-4 text-xs font-mono overflow-x-auto leading-relaxed\"><code id=\"code-snippet-${ep.id}\"></code></pre>\n                                </div>\n                            </div>\n\n                        </div>\n                    </div>\n                `;\n                container.insertAdjacentHTML('beforeend', cardHtml);\n                updateSnippet(ep.id);\n            });\n\n            updateCategoryCounts();\n        }\n\n        // Accordion Toggle\n        function toggleCard(id) {\n            const content = document.getElementById(`content-${id}`);\n            const chevron = document.getElementById(`chevron-${id}`);\n            const isHidden = content.classList.contains('hidden');\n            \n            if (isHidden) {\n                content.classList.remove('hidden');\n                chevron.classList.add('rotate-180');\n            } else {\n                content.classList.add('hidden');\n                chevron.classList.remove('rotate-180');\n            }\n        }\n\n        // Category Filter\n        function filterCategory(cat, el, e) {\n            if (e) e.preventDefault();\n            activeCategory = cat;\n            document.querySelectorAll('.cat-link').forEach(l => {\n                l.classList.remove('bg-gray-100', 'dark:bg-white/10', 'text-black', 'dark:text-white');\n                l.classList.add('text-gray-600', 'dark:text-gray-400');\n            });\n            if (el) {\n                el.classList.remove('text-gray-600', 'dark:text-gray-400');\n                el.classList.add('bg-gray-100', 'dark:bg-white/10', 'text-black', 'dark:text-white');\n            }\n            document.getElementById('sidebar').classList.add('-translate-x-full');\n            renderEndpoints();\n        }\n\n        // Category Counts Update\n        function updateCategoryCounts() {\n            const counts = { all: endpoints.length, bot: 0, dev: 0, new: endpoints.filter(e => e.isNew).length, fun: 0, weather: 0, money: 0, daily: 0, calc: 0, network: 0, verification: 0, turkey: 0, tools: 0, tempmail: 0 };\n            endpoints.forEach(ep => {\n                if (counts[ep.category] !== undefined) counts[ep.category]++;\n            });\n            Object.keys(counts).forEach(k => {\n                const el = document.getElementById(`count-${k}`);\n                if (el) el.innerText = counts[k];\n            });\n            const heroNew = document.getElementById('hero-new-count');\n            if (heroNew) heroNew.innerText = counts.new;\n        }\n\n        // Active Snippet Tab Tracking\n        const activeTabs = {};\n\n        function setTab(epId, lang) {\n            activeTabs[epId] = lang;\n            const parent = document.getElementById(`card-${epId}`);\n            parent.querySelectorAll('.tab-btn').forEach(btn => {\n                btn.classList.remove('bg-white', 'dark:bg-gray-900', 'text-gray-900', 'dark:text-white', 'shadow-sm');\n                btn.classList.add('text-gray-500');\n            });\n            const activeBtn = document.getElementById(`tab-${epId}-${lang}`);\n            if (activeBtn) {\n                activeBtn.classList.add('bg-white', 'dark:bg-gray-900', 'text-gray-900', 'dark:text-white', 'shadow-sm');\n                activeBtn.classList.remove('text-gray-500');\n            }\n            updateSnippet(epId);\n        }\n\n        // Construct Full Endpoint URL (path params + optional query params)\n        function getComputedUrl(ep) {\n            let path = ep.path;\n            const query = [];\n            ep.params.forEach(p => {\n                const input = document.getElementById(`input-${ep.id}-${p.name}`);\n                const raw = input ? input.value.trim() : '';\n                if (p.in === 'query') {\n                    const val = raw || (p.required ? p.default : '');\n                    if (val !== '') query.push(`${encodeURIComponent(p.name)}=${encodeURIComponent(val)}`);\n                } else {\n                    path = path.replace(`{${p.name}}`, encodeURIComponent(raw || p.default));\n                }\n            });\n            return `${API_BASE}${path}${query.length ? '?' + query.join('&') : ''}`;\n        }\n\n        // Generate Code Snippets Dynamic\n        function updateSnippet(epId) {\n            const ep = endpoints.find(e => e.id === epId);\n            if (!ep) return;\n\n            const targetLang = activeTabs[epId] || 'curl';\n            const url = getComputedUrl(ep);\n            const codeEl = document.getElementById(`code-snippet-${epId}`);\n\n            let snippet = '';\n\n            if (targetLang === 'curl') {\n                snippet = `curl -X ${ep.method} \"${url}\" \\\\\n  -H \"Accept: application/json\"`;\n            } else if (targetLang === 'fetch') {\n                snippet = `fetch(\"${url}\", {\n  method: \"${ep.method}\",\n  headers: { \"Accept\": \"application/json\" }\n})\n.then(response => response.json())\n.then(data => console.log(data))\n.catch(error => console.error(\"Hata:\", error));`;\n            } else if (targetLang === 'python') {\n                snippet = `import requests\n\nurl = \"${url}\"\nheaders = {\"Accept\": \"application/json\"}\n\nresponse = requests.${ep.method.toLowerCase()}(url, headers=headers)\nprint(response.json())`;\n            } else if (targetLang === 'node') {\n                snippet = `const axios = require('axios');\n\naxios.${ep.method.toLowerCase()}(\"${url}\")\n  .then(response => {\n    console.log(response.data);\n  })\n  .catch(error => {\n    console.error(error);\n  });`;\n            }\n\n            if (codeEl) codeEl.innerText = snippet;\n        }\n\n        // Open endpoint in a new browser tab (no fetch). POST endpoints use a form targeting a new tab.\n        function executeRequest(epId) {\n            const ep = endpoints.find(e => e.id === epId);\n            if (!ep) return;\n            const url = getComputedUrl(ep);\n            if (ep.method === 'POST') {\n                const form = document.createElement('form');\n                form.method = 'POST';\n                form.action = url;\n                form.target = '_blank';\n                document.body.appendChild(form);\n                form.submit();\n                document.body.removeChild(form);\n            } else {\n                window.open(url, '_blank', 'noopener');\n            }\n        }\n\n        // Copy Helper\n        function copyToClipboard(text) {\n            const done = () => showToast('Panoya kopyalandı!');\n            if (navigator.clipboard && window.isSecureContext) {\n                navigator.clipboard.writeText(text).then(done).catch(() => legacyCopy(text, done));\n            } else {\n                legacyCopy(text, done);\n            }\n        }\n\n        function legacyCopy(text, cb) {\n            const el = document.createElement('textarea');\n            el.value = text;\n            document.body.appendChild(el);\n            el.select();\n            document.execCommand('copy');\n            document.body.removeChild(el);\n            cb();\n        }\n\n        function copyCodeSnippet(epId) {\n            const codeEl = document.getElementById(`code-snippet-${epId}`);\n            if (codeEl) {\n                copyToClipboard(codeEl.innerText);\n            }\n        }\n\n        function showToast(msg) {\n            const toast = document.getElementById('toast');\n            document.getElementById('toast-message').innerText = msg;\n            toast.classList.remove('translate-y-20', 'opacity-0', 'pointer-events-none');\n            setTimeout(() => {\n                toast.classList.add('translate-y-20', 'opacity-0', 'pointer-events-none');\n            }, 2500);\n        }\n\n        // Theme Switcher Setup\n        const themeToggleBtn = document.getElementById('theme-toggle');\n        const darkIcon = document.getElementById('theme-dark-icon');\n        const lightIcon = document.getElementById('theme-light-icon');\n\n        function initTheme() {\n            let saved = null; try { saved = localStorage.getItem('theme'); } catch (e) {}\n            if (saved === 'light') {\n                document.documentElement.classList.remove('dark');\n                lightIcon.classList.remove('hidden');\n                darkIcon.classList.add('hidden');\n            } else {\n                document.documentElement.classList.add('dark');\n                darkIcon.classList.remove('hidden');\n                lightIcon.classList.add('hidden');\n            }\n        }\n\n        themeToggleBtn.addEventListener('click', () => {\n            if (document.documentElement.classList.contains('dark')) {\n                document.documentElement.classList.remove('dark');\n                try { localStorage.setItem('theme', 'light'); } catch (e) {}\n                lightIcon.classList.remove('hidden');\n                darkIcon.classList.add('hidden');\n            } else {\n                document.documentElement.classList.add('dark');\n                try { localStorage.setItem('theme', 'dark'); } catch (e) {}\n                darkIcon.classList.remove('hidden');\n                lightIcon.classList.add('hidden');\n            }\n        });\n\n        // Search Handlers\n        document.getElementById('endpoint-search').addEventListener('input', renderEndpoints);\n        document.getElementById('endpoint-search-mobile').addEventListener('input', renderEndpoints);\n\n        // Mobile Sidebar Toggle\n        const sidebar = document.getElementById('sidebar');\n        document.getElementById('mobile-menu-btn').addEventListener('click', () => {\n            sidebar.classList.toggle('-translate-x-full');\n        });\n\n        // Initial Initialization\n        window.addEventListener('DOMContentLoaded', () => {\n            initTheme();\n            renderEndpoints();\n        });\n    </script>\n</body>\n</html>", 'utf8');
