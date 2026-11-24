/* 연구진 대시보드 · AI 기반 초연결 지능도시 델파이 조사 (1·2·3차 통합)
 * 서버는 운영 시트를 읽기만 하고 원자료를 돌려준다. 모든 집계는 이 화면에서 계산한다.
 * 1차·2차는 레거시 집계 서버(l_ 접두사 테이블)에서, 3차는 전용 설문 서버에서 가져온다. */
(() => {
'use strict';
const CFG = Object.assign({ refreshSec: 60, r1Exclude: [] }, window.DASH_CONFIG || {});
const LOCAL = /[?&]local=1/.test(location.search);
const R1 = ['A', 'B', 'C', 'D', 'E', 'F'];
const R2 = ['R2A', 'R2B', 'R2C', 'R2D'];
const PK = ['R2A:R2B', 'R2A:R2C', 'R2A:R2D', 'R2B:R2C', 'R2B:R2D', 'R2C:R2D'];
const R3 = ['R3A', 'R3B', 'R3C', 'R3D'];
const PK3 = ['R3A:R3B', 'R3A:R3C', 'R3A:R3D', 'R3B:R3C', 'R3B:R3D', 'R3C:R3D'];
const RI = { 3: 0.58, 4: 0.9, 5: 1.12, 6: 1.24 };
const TH = { consensus: 0.75, convergence: 0.5, cv: 0.5, cr: 0.1 };
const TABS = [['overview', '종합'], ['progress', '응답 현황'], ['r1', '1차 결과'], ['r2', '2차 결과'], ['r3', '3차 결과'], ['opinions', '의견'], ['quality', '품질 점검'], ['method', '산식 · 기준']];
const KEY = 'aicity_dash_code';

const S = {
  code: sessionStorage.getItem(KEY) || localStorage.getItem(KEY) || '',
  raw: null, M: null, prevM: null, at: null, err: '', busy: false,
  tab: (location.hash || '').slice(1) || 'overview',
  hide: localStorage.getItem('aicity_dash_hide') === '1',
  auto: localStorage.getItem('aicity_dash_auto') !== '0',
  sort: {}, filt: { prog: 'open', svcType: 'all', ahp: 'ok', opSvc: 'all' }, csv: {}, printing: false
};
const app = document.getElementById('app');

/* ---------- 도구 ---------- */
const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const num = v => { if (v === null || v === '' || v === undefined) return null; const n = Number(v); return Number.isFinite(n) ? n : null; };
const f = (x, d = 2) => (x == null || !Number.isFinite(x) ? '-' : x.toFixed(d));
const pc = (x, d = 1) => (x == null || !Number.isFinite(x) ? '-' : x.toFixed(d) + '%');
const isTest = id => /^T/i.test(String(id || ''));
const mean = a => (a.length ? a.reduce((s, x) => s + x, 0) / a.length : null);
const gmean = a => (a.length ? Math.exp(a.reduce((s, x) => s + Math.log(x), 0) / a.length) : null);
function q(sorted, p) { const n = sorted.length; if (!n) return null; const h = (n - 1) * p, lo = Math.floor(h), hi = Math.ceil(h); return sorted[lo] + (h - lo) * (sorted[hi] - sorted[lo]); }
const LF = [0]; function lf(n) { for (let i = LF.length; i <= n; i++) LF[i] = LF[i - 1] + Math.log(i); return LF[n]; }
/* CVR 기준값: 이항분포(p=.5) 단측 .05 정확검정 (Ayre & Scally, 2014 방식) */
function cvrCrit(n) {
  if (!n) return null;
  let tail = 0;
  for (let k = n; k >= 0; k--) {
    const p = Math.exp(lf(n) - lf(k) - lf(n - k) - n * Math.LN2);
    if (tail + p > 0.05) return k === n ? 1 : (2 * (k + 1) / n) - 1;
    tail += p;
  }
  return -1;
}
function describe(vals, likert = true) {
  const v = vals.filter(x => x != null && Number.isFinite(x)).sort((a, b) => a - b);
  const n = v.length;
  if (!n) return { n: 0 };
  const m = mean(v);
  const sd = n > 1 ? Math.sqrt(v.reduce((s, x) => s + (x - m) ** 2, 0) / (n - 1)) : 0;
  const med = q(v, 0.5), q1 = q(v, 0.25), q3 = q(v, 0.75);
  const pos = v.filter(x => x >= 4).length;
  const o = { n, mean: m, sd, med, q1, q3, min: v[0], max: v[n - 1], pos, posPct: pos / n * 100,
    cvr: (pos - n / 2) / (n / 2), cvrCrit: cvrCrit(n), consensus: med ? 1 - (q3 - q1) / med : null, convergence: (q3 - q1) / 2, cv: m ? sd / m : null };
  if (likert) o.dist = [1, 2, 3, 4, 5].map(k => v.filter(x => x === k).length);
  return o;
}
function table(name) {
  const t = S.raw && S.raw.tables && S.raw.tables[name];
  if (!t || !t.rows) return null;
  return t.rows.map(r => { const o = {}; t.head.forEach((h, i) => { o[h] = r[i]; }); return o; });
}
function eig(A) {
  const n = A.length; let w = A.map(() => 1 / n);
  for (let it = 0; it < 1000; it++) {
    const nw = A.map(row => row.reduce((s, v, k) => s + v * w[k], 0));
    const sum = nw.reduce((a, b) => a + b, 0);
    const nn = nw.map(v => v / sum);
    const d = nn.reduce((s, v, k) => s + Math.abs(v - w[k]), 0);
    w = nn; if (d < 1e-14) break;
  }
  const Aw = A.map(row => row.reduce((s, v, k) => s + v * w[k], 0));
  const lambda = Aw.reduce((s, v, i) => s + v / w[i], 0) / n;
  const CI = (lambda - n) / (n - 1);
  return { w, lambda, CI, CR: RI[n] ? Math.max(0, CI / RI[n]) : 0 };
}
function matrix(row) {
  const A = R2.map((_, i) => R2.map((__, j) => (i === j ? 1 : null)));
  for (const k of PK) {
    const [a, b] = k.split(':'); const i = R2.indexOf(a), j = R2.indexOf(b); const x = num(row[k]);
    if (!x || x <= 0) return null;
    A[i][j] = x; A[j][i] = 1 / x;
  }
  return A;
}

function matrix3(p2) {
  const A = R3.map((_, i) => R3.map((__, j) => (i === j ? 1 : null)));
  for (const k of PK3) {
    const [a, b] = k.split(':'); const i = R3.indexOf(a), j = R3.indexOf(b); const x = p2[k];
    if (!x) return null;
    const vnum = Number(x.v) || 1;
    const ratio = x.side === 'R' ? 1 / vnum : vnum;
    if (!ratio || ratio <= 0) return null;
    A[i][j] = ratio; A[j][i] = 1 / ratio;
  }
  return A;
}
function groupAhp(mats) {
  if (!mats.length) return null;
  const G = R2.map((_, i) => R2.map((__, j) => (i === j ? 1 : gmean(mats.map(A => A[i][j])))));
  return Object.assign(eig(G), { n: mats.length, G });
}
const parseTime = s => { if (!s) return null; const m = String(s).match(/(\d{4})-(\d{2})-(\d{2})(?:[ T](\d{2}):(\d{2})(?::(\d{2}))?)?/); return m ? new Date(+m[1], +m[2] - 1, +m[3], +(m[4] || 0), +(m[5] || 0), +(m[6] || 0)) : null; };
const fmtT = d => d ? `${d.getMonth() + 1}/${d.getDate()} ${String(d.getHours()).padStart(2, '0')}:${String(d.getMinutes()).padStart(2, '0')}` : '-';
const fmtD = s => { const d = parseTime(s); if (!d) return '-'; const hasT = /\d{2}:\d{2}/.test(s) && !/ 00:00:00$/.test(s); return hasT ? fmtT(d) : `${d.getMonth() + 1}/${d.getDate()}`; };

/* ---------- 모델 ---------- */
function computeRound(names, svcs, w0) {
  const st = table(names.status);
  if (!st) return null;
  const status = st.filter(r => r['번호'] && !isTest(r['번호']));
  const subIds = new Set(status.filter(r => r['상태'] === '제출 완료').map(r => r['번호']));
  const rawP1 = (table(names.p1) || []).filter(r => !isTest(r['번호']));
  const rawP2 = (table(names.p2) || []).filter(r => !isTest(r['번호']));
  const rawP3 = (table(names.p3) || []).filter(r => !isTest(r['번호']));
  const p1 = rawP1.filter(r => subIds.has(r['번호']));
  const p2 = rawP2.filter(r => subIds.has(r['번호']));
  const p3 = rawP3.filter(r => subIds.has(r['번호']));
  // 이상 행
  const orphan = {};
  [['1부', rawP1], ['2부', rawP2], ['3부', rawP3]].forEach(([k, rows]) => rows.forEach(r => { if (!subIds.has(r['번호'])) { orphan[r['번호']] = orphan[r['번호']] || { id: r['번호'], parts: {} }; orphan[r['번호']].parts[k] = (orphan[r['번호']].parts[k] || 0) + 1; } }));
  const has1 = new Set(p1.map(r => r['번호'])), has2 = new Set(p2.map(r => r['번호'])), has3 = new Set(p3.map(r => r['번호']));
  const missing = [...subIds].filter(id => !has1.has(id) || !has2.has(id) || !has3.has(id));
  // 1부
  const items = R2.map(id => ({ id, ...describe(p1.map(r => num(r[id + '_점수']))) }));
  const overall = describe(p1.map(r => num(r['전체 점수'])));
  // 2부
  const indiv = p2.map(r => { const A = matrix(r); if (!A) return null; const e = eig(A); return { id: r['번호'], A, ...e, sheetCR: num(r['CR']) }; }).filter(Boolean);
  const okSet = indiv.filter(x => x.CR <= TH.cr + 1e-9);
  const gOk = groupAhp(okSet.map(x => x.A)), gAll = groupAhp(indiv.map(x => x.A));
  const aip = indiv.length ? (() => { const g = R2.map((_, k) => gmean(indiv.map(x => x.w[k]))); const s = g.reduce((a, b) => a + b, 0); return g.map(x => x / s); })() : null;
  const wDist = R2.map((_, k) => describe(indiv.map(x => x.w[k]), false));
  const W = (gOk && gOk.w) || (gAll && gAll.w) || w0 || R2.map(() => 0.25);
  // 3부
  const byRespSvc = {};
  p3.forEach(r => { const sid = r['서비스ID']; (byRespSvc[sid] = byRespSvc[sid] || []).push(r); });
  const services = svcs.map(s => {
    const rows = byRespSvc[s.id] || [];
    const crit = R2.map(id => describe(rows.map(r => num(r[id]))));
    const ws = rows.map(r => { const v = R2.map(id => num(r[id])); return v.every(x => x != null) ? v.reduce((a, x, k) => a + x * W[k], 0) : null; });
    const d = describe(ws, false);
    const means = crit.map(c => c.mean);
    return { ...s, n: rows.length, crit, simple: means.every(x => x != null) ? mean(means) : null, weighted: means.every(x => x != null) ? means.reduce((a, x, k) => a + x * W[k], 0) : null, wd: d, notes: rows.filter(r => String(r['의견'] || '').trim()).map(r => ({ id: r['번호'], txt: String(r['의견']).trim() })) };
  });
  const ranked = services.filter(s => s.weighted != null).sort((a, b) => b.weighted - a.weighted);
  let prev = null, rank = 0; ranked.forEach((s, i) => { const key = s.weighted.toFixed(6); if (key !== prev) rank = i + 1; s.rank = rank; prev = key; });
  // 일관 응답(3부 모든 점수 동일)
  const flat = {};
  p3.forEach(r => { const id = r['번호']; const vals = R2.map(k => num(r[k])); (flat[id] = flat[id] || new Set()); vals.forEach(v => flat[id].add(v)); });
  const straight = Object.entries(flat).filter(([, s]) => s.size === 1).map(([id, s]) => ({ id, v: [...s][0] }));
  const crMismatch = indiv.filter(x => x.sheetCR != null && Math.abs(x.sheetCR - x.CR) > 0.002);
  const subTimes = p1.map(r => parseTime(r['제출 시각'])).filter(Boolean);
  return { status, subIds, p1, p2, p3, orphan: Object.values(orphan), missing, items, overall, indiv, okSet, gOk, gAll, aip, wDist, W, services, ranked, straight, crMismatch, subTimes };
}


function computeR3(svcs, w0) {
  const roster = table('roster') || [];
  const status = roster.filter(r => r['번호'] && !isTest(r['번호']));
  const subIds = new Set(status.filter(r => r['상태'] === '제출 완료').map(r => r['번호']));
  const allResp = (S.raw.responses || []).filter(r => !isTest(r.id));
  const subResp = allResp.filter(r => subIds.has(r.id));
  const indiv = subResp.map(r => {
    const p2 = (r.responses && r.responses.p2) || {};
    const A = matrix3(p2); if (!A) return null;
    const e = eig(A); return Object.assign({ id: r.id, A, sheetCR: null }, e);
  }).filter(Boolean);
  const okSet = indiv.filter(x => x.CR <= TH.cr + 1e-9);
  const gOk = groupAhp(okSet.map(x => x.A)), gAll = groupAhp(indiv.map(x => x.A));
  const aip = indiv.length ? (() => { const g = R3.map((_, k) => gmean(indiv.map(x => x.w[k]))); const s = g.reduce((a, b) => a + b, 0); return g.map(x => x / s); })() : null;
  const wDist = R3.map((_, k) => describe(indiv.map(x => x.w[k]), false));
  const W = (gOk && gOk.w) || (gAll && gAll.w) || w0 || R3.map(() => 0.25);
  const byRespSvc = {};
  subResp.forEach(r => {
    const p3 = (r.responses && r.responses.p3) || {};
    const notes = (r.responses && r.responses.p3note) || {};
    Object.keys(p3).forEach(sid => {
      const q = p3[sid] || {};
      (byRespSvc[sid] = byRespSvc[sid] || []).push({ 번호: r.id, R3A: q.R3A, R3B: q.R3B, R3C: q.R3C, R3D: q.R3D, 의견: notes[sid] || '' });
    });
  });
  const services = svcs.map(s => {
    const rows = byRespSvc[s.id] || [];
    const crit = R3.map(id => describe(rows.map(r => num(r[id]))));
    const ws = rows.map(r => { const v = R3.map(id => num(r[id])); return v.every(x => x != null) ? v.reduce((a, x, k) => a + x * W[k], 0) : null; });
    const d = describe(ws, false);
    const means = crit.map(c => c.mean);
    return Object.assign({}, s, { n: rows.length, crit, simple: means.every(x => x != null) ? mean(means) : null, weighted: means.every(x => x != null) ? means.reduce((a, x, k) => a + x * W[k], 0) : null, wd: d, notes: rows.filter(r => String(r['의견'] || '').trim()).map(r => ({ id: r['번호'], txt: String(r['의견']).trim() })) });
  });
  const ranked = services.filter(s => s.weighted != null).sort((a, b) => b.weighted - a.weighted);
  let prev = null, rank = 0; ranked.forEach((s, i) => { const key = s.weighted.toFixed(6); if (key !== prev) rank = i + 1; s.rank = rank; prev = key; });
  const flat = {};
  subResp.forEach(r => { const p3 = (r.responses && r.responses.p3) || {}; const s = flat[r.id] = flat[r.id] || new Set(); Object.keys(p3).forEach(sid => { R3.forEach(k => s.add(num((p3[sid] || {})[k]))); }); });
  const straight = Object.entries(flat).filter(([, s]) => s.size === 1).map(([id, s]) => ({ id, v: [...s][0] }));
  return { status, subIds, indiv, okSet, gOk, gAll, aip, wDist, W, services, ranked, straight, items: null, overall: null, p1: [], p2: subResp, p3: [] };
}

function build() {
  const roster = table('l_roster') || [];
  const c1 = table('l_crit1') || [], c2 = table('l_crit2') || [];
  const crit1 = R1.map(id => { const r = c1.find(x => String(x[Object.keys(x)[0]]).trim().toUpperCase() === id) || {}; const v = Object.values(r); return { id, name: String(v[1] || id).trim(), def: String(v[2] || '').trim() }; });
  const crit2 = R2.map(id => {
    const r = c2.find(x => String(x['ID']).trim().toUpperCase() === id) || {};
    let sub = []; try { sub = JSON.parse(r['세부항목 구조(JSON)'] || '[]'); } catch (e) { sub = []; }
    return { id, name: String(r['평가항목'] || id).trim(), def: String(r['정의'] || '').trim(), details: String(r['세부내용(줄구분)'] || '').split(/\r?\n/).map(s => s.trim()).filter(Boolean), src: String(r['관련기존ID(쉼표)'] || '').split(',').map(s => s.trim().toUpperCase()).filter(Boolean), change: String(r['변경안내'] || '').trim(), sub: Array.isArray(sub) ? sub : [] };
  });
  const svcs = (table('l_svc') || []).filter(r => r['ID'] && String(r['사용 (예/아니오)'] || '예').trim() !== '아니오').map(r => ({ id: String(r['ID']).trim(), no: num(r['카드 번호']), name: String(r['서비스명'] || '').trim(), type: String(r['유형'] || '기타').trim(), summary: String(r['한 줄 요약'] || '').trim() }));
  const set = {}; (table('l_set') || []).forEach(r => { const v = Object.values(r); set[String(v[0]).trim()] = v[1]; });
  const r1rows = roster.filter(r => !isTest(r['번호']) && !CFG.r1Exclude.includes(r['번호']) && R1.every(k => [1, 2, 3, 4, 5].includes(num(r[k]))));
  const r1 = R1.map((id, i) => ({ ...crit1[i], ...describe(r1rows.map(r => num(r[id]))) }));
  const names = {}; roster.forEach(r => { names[r['번호']] = { name: r['성명'], org: r['소속'] }; });
  const rosterNotes = roster.filter(r => String(r['비고'] || '').trim()).map(r => ({ id: r['번호'], note: String(r['비고']).trim() }));
  const r2 = computeRound({ status: 'l_status', p1: 'l_p1', p2: 'l_p2', p3: 'l_p3' }, svcs);
  (r2 ? r2.status : []).forEach(r => { names[r['번호']] = names[r['번호']] || { name: r['성명'], org: r['소속'] }; });
  const r3roster = table('roster') || [];
  r3roster.forEach(r => { names[r['번호']] = names[r['번호']] || { name: r['성명'], org: r['소속유형'] }; });
  const r3 = computeR3(svcs, r2 && r2.W);
  return { roster, crit1, crit2, svcs, set, r1rows, r1, r2, r3, names, rosterNotes, r3roster, generatedAt: S.raw.generatedAt };
}

/* ---------- 서버 ---------- */
async function load(silent) {
  if (S.busy) return;
  S.busy = true; if (!silent) render();
  try {
    let res;
    if (LOCAL) res = await (await fetch('local_payload.json?t=' + Date.now())).json();
    else {
      const r = await fetch(CFG.api, { method: 'POST', headers: { 'Content-Type': 'text/plain;charset=utf-8' }, body: JSON.stringify({ code: S.code }) });
      res = await r.json();
    }
    if (!res.ok) {
      S.err = res.error === 'bad_code' ? '접속코드가 맞지 않습니다.' : res.error === 'locked' ? '접속 시도가 많아 10분간 잠겼습니다. 잠시 뒤 다시 시도해 주십시오.' : '자료를 불러오지 못했습니다. (' + esc(res.error) + ')';
      if (res.error === 'bad_code' || res.error === 'locked') { sessionStorage.removeItem(KEY); localStorage.removeItem(KEY); S.raw = null; S.M = null; }
    } else {
      S.err = '';
      const old = S.M;
      S.raw = res.data; S.M = build(); S.at = new Date();
      if (old) S.prevM = old;
    }
  } catch (e) {
    S.err = '연결이 원활하지 않습니다. 잠시 뒤 자동으로 다시 시도합니다.';
  }
  S.busy = false; render();
}
let timer = null;
function schedule() { clearInterval(timer); if (S.auto) timer = setInterval(() => { if (S.M && document.visibilityState === 'visible') load(true); }, CFG.refreshSec * 1000); }
setInterval(() => { const el = document.getElementById('ago'); if (el && S.at) el.textContent = ago(S.at); }, 5000);
function ago(d) { const s = Math.round((Date.now() - d) / 1000); return s < 60 ? `${s}초 전` : `${Math.floor(s / 60)}분 전`; }

/* ---------- 공통 렌더 조각 ---------- */
function who(id, withOrg) {
  const n = S.M.names[id] || {};
  if (S.hide) return `<b>${esc(id)}</b>`;
  return `<b>${esc(n.name || id)}</b> <span class="mute">${esc(id)}${withOrg && n.org ? ' · ' + esc(n.org) : ''}</span>`;
}
function dist(d, n) {
  if (!d || !n) return '';
  return `<div class="dist" title="1점 ${d[0]} · 2점 ${d[1]} · 3점 ${d[2]} · 4점 ${d[3]} · 5점 ${d[4]}">${d.map((c, i) => c ? `<span class="d${i + 1}" style="width:${c / n * 100}%">${c / n >= 0.07 ? c : ''}</span>` : '').join('')}</div>`;
}
const legend = () => `<div class="legend">${['1점', '2점', '3점', '4점', '5점'].map((t, i) => `<span><i style="background:var(--l${i + 1})"></i>${t}</span>`).join('')}</div>`;
function chipPass(ok, yes = '충족', no = '미충족') { return ok == null ? '<span class="chip mute">-</span>' : ok ? `<span class="chip ok">${yes}</span>` : `<span class="chip no">${no}</span>`; }
function delphiCols(extra = []) {
  return [
    { k: 'n', l: 'N', n: 1, fmt: x => x },
    { k: 'mean', l: '평균', n: 1, fmt: x => f(x), strong: 1 },
    { k: 'sd', l: '표준편차', n: 1, fmt: x => f(x) },
    { k: 'med', l: '중앙값', n: 1, fmt: x => f(x, 1) },
    { k: 'q1', l: 'Q1', n: 1, fmt: x => f(x, 2) },
    { k: 'q3', l: 'Q3', n: 1, fmt: x => f(x, 2) },
    { k: 'posPct', l: '4·5점', n: 1, fmt: x => pc(x) },
    { k: 'cvr', l: 'CVR', n: 1, fmt: (x, r) => `${f(x)} ${chipPass(r.cvrCrit == null ? null : x >= r.cvrCrit - 1e-9, '통과', '미달')}`, csv: x => f(x) },
    { k: 'consensus', l: '합의도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x >= TH.consensus - 1e-9)}`, csv: x => f(x) },
    { k: 'convergence', l: '수렴도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x <= TH.convergence + 1e-9)}`, csv: x => f(x) },
    { k: 'cv', l: '변이계수', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x <= TH.cv + 1e-9, '안정', '불안정')}`, csv: x => f(x) },
    ...extra
  ];
}
/* 정렬·CSV 가능한 표 */
function tbl(id, cols, rows, opt = {}) {
  const st = S.sort[id];
  let data = rows.slice();
  if (st) { const c = cols.find(c => c.k === st.k); if (c) { const val = r => (c.sv ? c.sv(r) : r[c.k]); data.sort((a, b) => { const x = val(a), y = val(b); if (x == null) return 1; if (y == null) return -1; return (typeof x === 'number' && typeof y === 'number' ? x - y : String(x).localeCompare(String(y), 'ko', { numeric: true })) * st.d; }); } }
  S.csv[id] = { name: opt.file || id, cols, rows: data };
  const th = cols.map(c => `<th class="${c.n ? 'n' : ''}" data-sort="${id}|${c.k}" title="${esc(c.t || '')}">${esc(c.l)}${st && st.k === c.k ? `<span class="ar">${st.d > 0 ? '▲' : '▼'}</span>` : ''}</th>`).join('');
  const tb = data.map(r => `<tr>${cols.map(c => `<td class="${c.n ? 'n' : ''}${c.strong ? ' strong' : ''}">${c.fmt ? c.fmt(r[c.k], r) : esc(r[c.k])}</td>`).join('')}</tr>`).join('');
  return `<div class="tbl-tools"><div class="left">${opt.tools || ''}</div><button class="btn" data-csv="${id}">CSV 내려받기</button></div><div class="tbl-wrap" style="${opt.maxh ? 'max-height:' + opt.maxh + 'px' : ''}"><table><thead><tr>${th}</tr></thead><tbody>${tb || `<tr><td colspan="${cols.length}" class="mute" style="text-align:center;padding:22px">자료 없음</td></tr>`}</tbody></table></div>`;
}
function hbars(items, max, fmtv = x => f(x)) {
  return `<div class="hbars">${items.map(it => `<div class="hb"><div><div class="lab" title="${esc(it.label)}">${it.pre ? `<b>${esc(it.pre)}</b>` : ''}${esc(it.label)}</div><div class="trk"><i style="width:${Math.max(0, Math.min(100, (it.v - (it.min || 0)) / (max - (it.min || 0)) * 100))}%;${it.color ? 'background:' + it.color : ''}"></i></div></div><div class="v">${fmtv(it.v)}</div></div>`).join('')}</div>`;
}
const sec = (h, p, right = '') => `<div class="sec-title"><div><h2>${h}</h2>${p ? `<p>${p}</p>` : ''}</div>${right}</div>`;

/* ---------- 화면 ---------- */
function render() {
  if (!S.M) {
    if (S.code && S.busy) { app.innerHTML = `<div class="loading"><div class="spin"></div>자료를 불러오는 중입니다</div>`; return; }
    return renderGate();
  }
  const M = S.M, r2 = M.r2;
  const sub = r2 ? r2.subIds.size : 0, tot = r2 ? r2.status.length : 0;
  const prevSub = S.prevM && S.prevM.r2 ? S.prevM.r2.subIds.size : null;
  S.csv = {};
  const body = S.printing ? TABS.map(([k, l], i) => `<section class="page"><div class="print-only" style="font-size:11px;color:#667085;margin-bottom:6px">${esc(l)}</div>${view(k)}</section>`).join('') : view(S.tab);
  app.innerHTML = `
  <header class="top"><div class="top-in">
    <div class="top-row">
      <div class="brand"><div class="eyebrow"><b>연구진 전용</b> · AI 기반 초연결 지능도시 전문가 델파이 조사</div><h1>조사 결과 대시보드</h1></div>
      <div class="stamp"><span class="live-dot ${S.auto ? '' : 'off'}"></span>기준 <b>${esc(fmtD(M.generatedAt) === '-' ? M.generatedAt : fmtT(parseTime(M.generatedAt)))}</b> · <span id="ago">${S.at ? ago(S.at) : ''}</span><br>2차 제출 <b>${sub}/${tot}</b>${prevSub != null && sub > prevSub ? `<span class="delta">+${sub - prevSub}</span>` : ''} · 3차 제출 <b>${M.r3.subIds.size}/${M.r3.status.length}</b></div>
      <div class="tools">
        <button class="btn ${S.auto ? 'on' : ''}" data-act="auto" title="${CFG.refreshSec}초마다 새로 읽기">자동 갱신 ${S.auto ? '켬' : '끔'}</button>
        <button class="btn" data-act="reload">${S.busy ? '읽는 중…' : '새로고침'}</button>
        <button class="btn ${S.hide ? 'on' : ''}" data-act="hide" title="회의 화면용: 이름·소속을 번호로 가림">이름 가리기</button>
        <button class="btn" data-act="print">인쇄 · PDF</button>
        <button class="btn" data-act="logout">나가기</button>
      </div>
    </div>
    <nav class="nav">${TABS.map(([k, l]) => `<button data-tab="${k}" class="${S.tab === k ? 'cur' : ''}">${l}</button>`).join('')}</nav>
  </div></header>
  <main>
    ${S.err ? `<div class="notice"><b>알림</b><span>${S.err}</span></div>` : ''}
    <div class="notice no-print"><b>실시간 수치</b><span>운영 시트를 그대로 읽어 계산한 값입니다. 진행 중인 차수는 숫자가 계속 바뀝니다. 보고서와 회의자료에는 기준 시각을 함께 적으십시오. 시험 계정(T로 시작)은 모두 제외했습니다.</span></div>
    ${body}
  </main>`;
}

function renderGate() {
  app.innerHTML = `<div class="gate"><form class="gate-card" id="gate">
    <span class="eyebrow">연구진 전용</span>
    <h1>AI 기반 초연결 지능도시<br>델파이 조사 결과 대시보드</h1>
    <p>1차·2차·3차 조사 결과를 실시간으로 봅니다. 응답자 개인정보가 포함되어 있으니 연구진 외 공유를 삼가 주십시오.</p>
    <label for="code">접속코드</label>
    <input id="code" type="password" autocomplete="off" autocapitalize="characters" spellcheck="false" placeholder="XXXXX-XXXXX" required>
    <div class="row"><input id="remember" type="checkbox"><label for="remember" style="font-weight:500;color:var(--muted)">이 기기에서 기억 (개인 기기에서만)</label></div>
    <button class="btn primary" type="submit">${S.busy ? '확인 중…' : '들어가기'}</button>
    <div class="err">${S.err || ''}</div>
  </form></div>`;
  const fm = document.getElementById('gate');
  fm.addEventListener('submit', e => {
    e.preventDefault();
    S.code = document.getElementById('code').value.trim();
    if (!S.code && !LOCAL) return;
    sessionStorage.setItem(KEY, S.code);
    if (document.getElementById('remember').checked) localStorage.setItem(KEY, S.code);
    load();
  });
  setTimeout(() => { const c = document.getElementById('code'); if (c) c.focus(); }, 30);
}

function view(k) {
  try {
    return ({ overview: vOverview, progress: vProgress, r1: vR1, r2: vR2, r3: vR3, opinions: vOpinions, quality: vQuality, method: vMethod }[k] || vOverview)();
  } catch (e) { console.error(e); return `<div class="empty">이 화면을 그리는 중 오류가 났습니다: ${esc(e.message)}</div>`; }
}

/* 종합 */
function vOverview() {
  const M = S.M, r2 = M.r2;
  const cnt = statusCount(r2);
  const tot = r2.status.length, sub = r2.subIds.size;
  const top = r2.ranked.slice(0, 10);
  const maxW = Math.max(...r2.W);
  const itemsOk = r2.items.filter(i => i.n && i.cvr >= i.cvrCrit - 1e-9 && i.consensus >= TH.consensus - 1e-9 && i.convergence <= TH.convergence + 1e-9).length;
  return `
  ${sec('한눈에 보기', '1차 결과는 확정값, 2차는 진행 중 실시간 값입니다.')}
  <div class="grid g4">
    <div class="card kpi"><div class="label">1차 조사 응답</div><div class="val">${M.r1rows.length}<small>명</small></div><div class="foot">6개 평가항목 · 2차 화면 제시 기준</div></div>
    <div class="card kpi"><div class="label">2차 제출 완료</div><div class="val">${sub}<small>/ ${tot}명</small></div><div class="bar"><i style="width:${sub / tot * 100}%;background:var(--ink)"></i><i style="width:${cnt['진행 중'] / tot * 100}%;background:#8ea3c8"></i></div><div class="foot">응답률 ${pc(sub / tot * 100)} · 작성 중 ${cnt['진행 중']}명</div></div>
    <div class="card kpi"><div class="label">2차 미제출</div><div class="val">${tot - sub}<small>명</small></div><div class="foot">작성 중 ${cnt['진행 중']} · 접속만 ${cnt['접속']} · 미접속 ${cnt['미접속']}</div></div>
    <div class="card kpi"><div class="label">3차 조사</div><div class="val" style="font-size:20px;margin-top:10px">${M.r3.status.length ? `${M.r3.subIds.size}<small>/ ${M.r3.status.length}명 제출</small>` : '준비 중'}</div><div class="foot">${esc(M.set['3차 일정 문구'] || '')}</div></div>
  </div>

  ${sec('평가체계의 변화: 1차 6개 항목 → 2차 4개 항목', '선은 관련 기존 항목(비교 참고)이며, 1차 응답을 2차 항목으로 옮겨 계산하지 않았습니다.')}
  <div class="card flow">${flowSvg()}</div>

  <div class="grid g2" style="margin-top:14px">
    <div class="card"><h3>2차 평가항목 적절성 (5점)</h3><p class="sub">델파이 기준 3가지(CVR · 합의도 · 수렴도)를 모두 충족한 항목 ${itemsOk}/4개</p>
      ${hbars(r2.items.map(i => ({ label: M.crit2.find(c => c.id === i.id).name, pre: i.id.slice(-1), v: i.mean, min: 1 })), 5)}
      <div class="foot-note">전체 구성 적절성 평균 ${f(r2.overall.mean)} (N=${r2.overall.n || 0})</div></div>
    <div class="card"><h3>2차 평가항목 가중치 (AHP)</h3><p class="sub">일관성(CR ≤ 0.1) 충족 ${r2.okSet.length}명의 판단을 기하평균으로 합친 값${r2.gOk ? ` · 통합 CR ${f(r2.gOk.CR, 3)}` : ''}</p>
      ${hbars(r2.W.map((w, k) => ({ label: M.crit2[k].name, pre: R2[k].slice(-1), v: w * 100 })), Math.ceil(maxW * 100 / 10) * 10 + 5, x => f(x, 1) + '%')}
      <div class="foot-note">전원(${r2.indiv.length}명) 기준과의 비교는 「2차 결과」에서 볼 수 있습니다.</div></div>
  </div>

  ${sec('2차 후보 서비스 상위 10개', `가중 종합점수 = 기준별 평균 × AHP 가중치의 합 (5점 만점) · 평가 ${r2.ranked.length ? r2.ranked[0].n : 0}명`)}
  <div class="card">${top.length ? hbars(top.map(s => ({ label: `${s.name}`, pre: String(s.rank), v: s.weighted, min: 1 })), 5) : '<div class="empty">아직 제출된 3부 응답이 없습니다.</div>'}

  ${M.r3.status.length ? `
  ${sec('3차 조사 한눈에 보기', `제출 완료 ${M.r3.subIds.size}/${M.r3.status.length}명 · 2차 결과를 재평가합니다`)}
  <div class="grid g2">
    <div class="card"><h3>3차 가중치 vs 2차 가중치</h3><p class="sub">통합 가중치(기본: CR≤0.1) 비교</p>
      ${hbars(R3.map((id,k)=>({label:M.crit2[k].name+' (3차)', pre:id.slice(-1), v:M.r3.W[k]*100, min:0})).concat(R2.map((id,k)=>({label:M.crit2[k].name+' (2차 참고)', pre:id.slice(-1), v:r2.W[k]*100, min:0, color:'#b8c2d3'}))), Math.ceil(Math.max(...M.r3.W,...r2.W)*100/10)*10+5, x=>f(x,1)+'%')}
    </div>
    <div class="card"><h3>3차 서비스 순위 상위 10개</h3><p class="sub">가중 종합점수 기준${M.r3.ranked.length?'':' · 아직 제출된 응답 없음'}</p>
      ${M.r3.ranked.length ? hbars(M.r3.ranked.slice(0,10).map(s=>({label:s.name, pre:String(s.rank), v:s.weighted, min:1})), 5) : '<div class="empty">아직 제출된 3부 응답이 없습니다.</div>'}
    </div>
  </div>` : ''}</div>`;
}
function statusCount(r) { const c = { '제출 완료': 0, '진행 중': 0, '접속': 0, '미접속': 0 }; r.status.forEach(x => { c[x['상태']] = (c[x['상태']] || 0) + 1; }); return c; }

function flowSvg() {
  const M = S.M, W = 960, rowH = 46, H = Math.max(R1.length, R2.length) * rowH + 40;
  const lx = 20, lw = 330, rx = 610, rw = 330;
  const ly = i => 30 + i * rowH, ry = i => 30 + i * (rowH * R1.length / R2.length) + (rowH * R1.length / R2.length - rowH) / 2;
  let s = `<svg viewBox="0 0 ${W} ${H}" xmlns="http://www.w3.org/2000/svg" font-family="Pretendard Variable, Pretendard, sans-serif">`;
  s += `<text x="${lx}" y="16" font-size="12" fill="#667085" font-weight="700">1차 · 6개 항목 (평균 · 4·5점 비율)</text><text x="${rx}" y="16" font-size="12" fill="#667085" font-weight="700">2차 · 4개 항목 (실시간 평균)</text>`;
  M.crit2.forEach((c, j) => c.src.forEach(sid => { const i = R1.indexOf(sid); if (i < 0) return; const y1 = ly(i) + 17, y2 = ry(j) + 17; s += `<path d="M${lx + lw} ${y1} C ${lx + lw + 130} ${y1}, ${rx - 130} ${y2}, ${rx} ${y2}" stroke="#b9c6e4" stroke-width="2" fill="none"/>`; }));
  M.r1.forEach((c, i) => { s += `<rect x="${lx}" y="${ly(i)}" width="${lw}" height="34" rx="8" fill="#fff" stroke="#e1e5ec"/><text x="${lx + 14}" y="${ly(i) + 22}" font-size="13.5" fill="#0d1626"><tspan font-weight="700" fill="#667085">${c.id}</tspan>  ${esc(c.name)}</text><text x="${lx + lw - 12}" y="${ly(i) + 22}" font-size="12.5" text-anchor="end" fill="#2b3546" font-weight="700">${f(c.mean)} · ${f(c.posPct, 0)}%</text>`; });
  M.crit2.forEach((c, j) => { const it = M.r2.items[j]; s += `<rect x="${rx}" y="${ry(j)}" width="${rw}" height="34" rx="8" fill="#0d1626"/><text x="${rx + 14}" y="${ry(j) + 22}" font-size="13.5" fill="#fff"><tspan font-weight="700" fill="#9fb3e6">${c.id.slice(-1)}</tspan>  ${esc(c.name)}</text><text x="${rx + rw - 12}" y="${ry(j) + 22}" font-size="12.5" text-anchor="end" fill="#fff" font-weight="700">${f(it.mean)}</text>`; });
  return s + '</svg>';
}

/* 응답 현황 */
function vProgress() {
  const M = S.M, r2 = M.r2, cnt = statusCount(r2), tot = r2.status.length;
  const order = { '진행 중': 0, '접속': 1, '미접속': 2, '제출 완료': 3 };
  const fl = S.filt.prog;
  const rows = r2.status.filter(r => fl === 'all' ? true : fl === 'open' ? r['상태'] !== '제출 완료' : r['상태'] === fl).map(r => ({ ...r, _p: num(r['진행률']) || 0, _o: order[r['상태']] ?? 9 }))
    .sort((a, b) => a._o - b._o || b._p - a._p || String(a['번호']).localeCompare(b['번호']));
  const segs = [['제출 완료', 'var(--ink)'], ['진행 중', '#8ea3c8'], ['접속', '#c9d3e6'], ['미접속', '#eceff3']];
  const cols = [
    { k: '번호', l: '번호' },
    { k: '성명', l: '성명', fmt: (x, r) => S.hide ? '<span class="mute">가림</span>' : esc(x) },
    { k: '소속', l: '소속', fmt: (x) => S.hide ? '<span class="mute">가림</span>' : esc(x) },
    { k: '상태', l: '상태', fmt: x => `<span class="chip ${x === '제출 완료' ? 'ok' : x === '진행 중' ? 'acc' : x === '접속' ? 'warn' : 'mute'}">${esc(x)}</span>` },
    { k: '_p', l: '진행률', n: 1, fmt: x => pc(x * 100, 0) },
    { k: '1부', l: '1부' }, { k: '2부', l: '2부' }, { k: '3부', l: '3부', sv: r => num(String(r['3부']).split('/')[0]) },
    { k: '최근 저장', l: '최근 저장', fmt: x => esc(fmtD(x)) },
    { k: '제출 시각', l: '제출', fmt: x => esc(fmtD(x)) }
  ];
  const tools = `<div class="seg">${[['open', '미제출'], ['진행 중', '작성 중'], ['접속', '접속만'], ['미접속', '미접속'], ['제출 완료', '제출 완료'], ['all', '전체']].map(([k, l]) => `<button data-filt="prog|${k}" class="${fl === k ? 'cur' : ''}">${l}</button>`).join('')}</div>`;
  return `
  ${sec('2차 조사 응답 현황', `대상 ${tot}명 · 마감(내부) ${esc(String(M.set['마감 일시'] || '-'))} · 응답자 화면 표기 기간 ${esc(String(M.set['조사 기간 문구'] || '-'))}`)}
  <div class="grid g21">
    <div class="card"><h3>상태 분포</h3><p class="sub">제출 ${cnt['제출 완료']} · 작성 중 ${cnt['진행 중']} · 접속만 ${cnt['접속']} · 미접속 ${cnt['미접속']}</p>
      <div class="bar" style="height:30px;border-radius:8px">${segs.map(([k, c]) => `<i style="width:${cnt[k] / tot * 100}%;background:${c}" title="${k} ${cnt[k]}명"></i>`).join('')}</div>
      <div class="legend" style="margin-top:10px">${segs.map(([k, c]) => `<span><i style="background:${c};border:1px solid #d0d5dd"></i>${k} ${cnt[k]}명 (${pc(cnt[k] / tot * 100, 0)})</span>`).join('')}</div>
      <h3 style="margin-top:22px">미제출자의 부별 완료</h3><p class="sub">제출 전 ${tot - cnt['제출 완료']}명 중 각 부를 다 마친 사람</p>
      ${(() => { const open = r2.status.filter(r => r['상태'] !== '제출 완료'); const done = k => open.filter(r => { const m = String(r[k] || '').split('/'); return m.length === 2 && m[0] === m[1] && +m[1] > 0; }).length; return hbars([['1부 평가항목', '1부'], ['2부 쌍대비교', '2부'], ['3부 서비스 평가', '3부']].map(([l, k]) => ({ label: l, v: done(k) })), Math.max(1, open.length), x => x + '명'); })()}
    </div>
    <div class="card"><h3>누적 제출 추이</h3><p class="sub">1부 결과 행의 제출 시각 기준</p>${cumChart(r2.subTimes, tot)}</div>
  </div>
  ${r2.orphan.length || r2.missing.length ? `<div class="notice" style="margin-top:14px"><b>확인 필요</b><span>${r2.orphan.map(o => `${esc(o.id)}: 결과 행(${Object.entries(o.parts).map(([k, v]) => k + ' ' + v).join(', ')})은 있으나 현황 탭 상태가 「제출 완료」가 아님. 집계에서 제외 중.`).join('<br>')}${r2.missing.map(id => `<br>${esc(id)}: 「제출 완료」이나 결과 행 일부 없음`).join('')}</span></div>` : ''}
  ${sec('응답자별 진행 상황', '독려 대상 확인용 · 열 제목을 누르면 정렬됩니다.')}
  ${tbl('progress', cols, rows, { tools, file: '2차_응답현황' })}
  ${M.r3.status.length ? `
  ${sec('3차 조사 응답 현황', `대상 ${M.r3.status.length}명 · 제출 완료 ${M.r3.subIds.size}명`)}
  ${(() => { const rows3 = M.r3.status.map(r => ({ 번호: r['번호'], 성명: r['성명'], 소속: r['소속유형'], 상태: r['상태'], 진행률: r['총 진행률'], 저장: r['최근 저장'], 제출: r['제출 시각'] })); const cols3 = [ { k: '번호', l: '번호' }, { k: '성명', l: '성명', fmt: x => S.hide ? '<span class="mute">가림</span>' : esc(x) }, { k: '소속', l: '소속', fmt: x => S.hide ? '<span class="mute">가림</span>' : esc(x) }, { k: '상태', l: '상태', fmt: x => `<span class="chip ${x === '제출 완료' ? 'ok' : x === '진행 중' ? 'acc' : x === '접속만' ? 'warn' : 'mute'}">${esc(x)}</span>` }, { k: '진행률', l: '진행률' }, { k: '저장', l: '최근 저장' }, { k: '제출', l: '제출 시각' } ]; return tbl('r3progress', cols3, rows3, { file: '3차_응답현황' }); })()}` : ''}`;
}
function cumChart(times, tot) {
  if (!times.length) return '<div class="empty">아직 제출이 없습니다.</div>';
  const t = times.slice().sort((a, b) => a - b);
  const W = 520, H = 190, P = { l: 34, r: 14, t: 12, b: 26 };
  const t0 = new Date(t[0]); t0.setHours(0, 0, 0, 0);
  const t1 = new Date(Math.max(Date.now(), +t[t.length - 1]));
  const x = d => P.l + (d - t0) / (t1 - t0) * (W - P.l - P.r);
  const y = v => H - P.b - v / tot * (H - P.t - P.b);
  let path = `M${x(t0)} ${y(0)}`; t.forEach((d, i) => { path += ` L${x(d)} ${y(i)} L${x(d)} ${y(i + 1)}`; }); path += ` L${x(t1)} ${y(t.length)}`;
  let g = '';
  [0, 0.25, 0.5, 0.75, 1].forEach(p => { g += `<line x1="${P.l}" x2="${W - P.r}" y1="${y(tot * p)}" y2="${y(tot * p)}" stroke="#eef0f3"/><text x="${P.l - 6}" y="${y(tot * p) + 4}" font-size="10" text-anchor="end" fill="#98a2b3">${Math.round(tot * p)}</text>`; });
  for (let d = new Date(t0); d <= t1; d.setDate(d.getDate() + 1)) g += `<line x1="${x(d)}" x2="${x(d)}" y1="${P.t}" y2="${H - P.b}" stroke="#eef0f3"/><text x="${x(d) + 3}" y="${H - 8}" font-size="10" fill="#98a2b3">${d.getMonth() + 1}/${d.getDate()}</text>`;
  return `<svg class="svgchart" viewBox="0 0 ${W} ${H}">${g}<path d="${path} L${x(t1)} ${y(0)} Z" fill="#eaf0fd" stroke="none"/><path d="${path}" fill="none" stroke="#1f4fd1" stroke-width="2"/><circle cx="${x(t1)}" cy="${y(t.length)}" r="4" fill="#1f4fd1"/><text x="${x(t1) - 6}" y="${y(t.length) - 8}" font-size="11" font-weight="700" text-anchor="end" fill="#0d1626">${t.length}명</text></svg>`;
}

/* 1차 */
function vR1() {
  const M = S.M;
  const cols = [{ k: 'id', l: '항목' }, { k: 'name', l: '평가항목', strong: 1 }, ...delphiCols(), { k: 'dist', l: '분포 (1~5점)', fmt: (x, r) => dist(x, r.n), csv: x => (x || []).join('/') }];
  const ex = CFG.r1Exclude.filter(Boolean);
  return `
  ${sec('1차 조사 결과 · 6개 평가항목', `N=${M.r1rows.length} · 5점 척도 "우수 서비스 선정 기준으로 적절한가"${ex.length ? ` · ${ex.join(', ')}는 1차 마감 뒤 도착해 이 통계에서 제외(2차 화면 제시 기준과 동일)` : ''}`, legend())}
  ${tbl('r1', cols, M.r1, { file: '1차_평가항목_통계' })}
  <div class="foot-note">CVR 기준값(N=${M.r1rows.length}): ${f(cvrCrit(M.r1rows.length), 3)} · 합의도 ≥ ${TH.consensus} · 수렴도 ≤ ${TH.convergence} · 변이계수 ≤ ${TH.cv}. 산식은 「산식 · 기준」 참고.</div>`;
}

/* 2차 */
function vR2() {
  const M = S.M, r2 = M.r2;
  const r1map = {}; M.r1.forEach(c => { r1map[c.id] = c; });
  const items = r2.items.map((it, k) => ({ ...it, name: M.crit2[k].name, ref: M.crit2[k].src.map(s => `${s} ${f(r1map[s] && r1map[s].mean)}`).join(', ') }));
  const all = [...items, { id: '전체', name: '전체 구성 적절성', ...r2.overall, ref: '' }];
  const cols1 = [{ k: 'id', l: '항목', fmt: x => esc(x === '전체' ? '전체' : x.slice(-1)) }, { k: 'name', l: '평가항목', strong: 1 }, ...delphiCols(), { k: 'dist', l: '분포', fmt: (x, r) => dist(x, r.n), csv: x => (x || []).join('/') }, { k: 'ref', l: '1차 관련 항목 평균 (참고)', fmt: x => `<span class="mute">${esc(x)}</span>` }];
  // 2부
  const G = S.filt.ahp === 'all' ? r2.gAll : r2.gOk;
  const Wsel = G ? G.w : null;
  const crPass = r2.indiv.length ? r2.okSet.length / r2.indiv.length * 100 : null;
  const wMax = Math.max(0.4, Math.ceil(Math.max(...r2.wDist.map(d => d.max || 0), ...(Wsel || [0])) * 10) / 10);
  const wrows = R2.map((id, k) => {
    const d = r2.wDist[k]; const sc = v => (v / wMax * 100);
    return `<div class="wrow"><div class="nm">${esc(M.crit2[k].name)}<small>개인 가중치 중앙값 ${f(d.med * 100, 1)}% · 범위 ${f(d.min * 100, 0)}~${f(d.max * 100, 0)}%</small></div>
      <div class="wtrack"><div class="axis"></div>${d.n ? `<div class="wh" style="left:${sc(d.min)}%;width:${sc(d.max - d.min)}%"></div><div class="box" style="left:${sc(d.q1)}%;width:${Math.max(0.5, sc(d.q3 - d.q1))}%"></div><div class="med" style="left:${sc(d.med)}%"></div>` : ''}${Wsel ? `<div class="grp" style="left:${sc(Wsel[k])}%" title="통합 가중치"></div>` : ''}</div>
      <div class="v">${Wsel ? f(Wsel[k] * 100, 1) + '%' : '-'}</div></div>`;
  }).join('');
  const ahpTools = `<div class="seg">${[['ok', `CR ≤ 0.1 (${r2.okSet.length}명)`], ['all', `전원 (${r2.indiv.length}명)`]].map(([k, l]) => `<button data-filt="ahp|${k}" class="${S.filt.ahp === k ? 'cur' : ''}">${l}</button>`).join('')}</div>`;
  const wcmp = R2.map((id, k) => ({ id, name: M.crit2[k].name, ok: r2.gOk ? r2.gOk.w[k] * 100 : null, all: r2.gAll ? r2.gAll.w[k] * 100 : null, aip: r2.aip ? r2.aip[k] * 100 : null, med: r2.wDist[k].med * 100 }));
  const cmpCols = [{ k: 'name', l: '평가항목', strong: 1 }, { k: 'ok', l: 'CR≤0.1 통합(AIJ)', n: 1, fmt: x => f(x, 1) + '%' }, { k: 'all', l: '전원 통합(AIJ)', n: 1, fmt: x => f(x, 1) + '%' }, { k: 'aip', l: '개인 가중치 기하평균(AIP)', n: 1, fmt: x => f(x, 1) + '%' }, { k: 'med', l: '개인 가중치 중앙값', n: 1, fmt: x => f(x, 1) + '%' }];
  // 3부
  const types = ['all', ...Array.from(new Set(M.svcs.map(s => s.type)))];
  const st = S.filt.svcType;
  const svRows = r2.ranked.filter(s => st === 'all' || s.type === st).map(s => ({ ...s, c0: s.crit[0].mean, c1: s.crit[1].mean, c2: s.crit[2].mean, c3: s.crit[3].mean, wpos: s.wd.posPct, wcons: s.wd.consensus, wconv: s.wd.convergence, wcv: s.wd.cv, nn: s.notes.length }));
  const svCols = [
    { k: 'rank', l: '순위', n: 1 }, { k: 'id', l: 'ID' }, { k: 'name', l: '서비스명', strong: 1 }, { k: 'type', l: '유형', fmt: x => `<span class="mute">${esc(x)}</span>` },
    { k: 'weighted', l: '가중 종합', n: 1, fmt: x => `<b>${f(x)}</b>` }, { k: 'simple', l: '단순 평균', n: 1, fmt: x => f(x) },
    ...R2.map((id, k) => ({ k: 'c' + k, l: id.slice(-1) + ' ' + M.crit2[k].name.split(' ')[0], t: M.crit2[k].name, n: 1, fmt: x => f(x) })),
    { k: 'wpos', l: '4점 이상', n: 1, fmt: x => pc(x, 0), t: '응답자별 가중점수 4.0 이상 비율' },
    { k: 'wcons', l: '합의도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x >= TH.consensus - 1e-9)}`, csv: x => f(x) },
    { k: 'wconv', l: '수렴도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x <= TH.convergence + 1e-9)}`, csv: x => f(x) },
    { k: 'wcv', l: '변이계수', n: 1, fmt: x => f(x) }, { k: 'n', l: 'N', n: 1 }, { k: 'nn', l: '의견', n: 1 }
  ];
  const svTools = `<select class="btn" data-sel="svcType">${types.map(t => `<option value="${esc(t)}" ${t === st ? 'selected' : ''}>${t === 'all' ? '유형 전체' : esc(t)}</option>`).join('')}</select>`;
  // 유형별
  const byType = {}; r2.ranked.forEach(s => { (byType[s.type] = byType[s.type] || []).push(s.weighted); });
  const typeRows = Object.entries(byType).map(([t, a]) => ({ type: t, cnt: a.length, avg: mean(a), max: Math.max(...a) })).sort((a, b) => b.avg - a.avg);
  return `
  ${sec('2차 1부 · 개편 평가항목 4개의 적절성', `제출 완료 ${r2.p1.length}명 · 5점 척도`, legend())}
  ${tbl('r2items', cols1, all, { file: '2차_1부_평가항목_통계' })}
  <div class="foot-note">CVR 기준값(N=${r2.p1.length}): ${f(cvrCrit(r2.p1.length), 3)}. 1차 관련 항목 평균은 비교 참고용이며, 같은 항목을 다시 잰 값이 아닙니다.</div>

  ${sec('2차 2부 · 평가항목 가중치 (AHP 쌍대비교)', `응답 ${r2.indiv.length}명 중 일관성 CR ≤ 0.1 충족 ${r2.okSet.length}명 (${pc(crPass)})${G ? ` · 통합 행렬 CR ${f(G.CR, 3)}` : ''}`, ahpTools)}
  <div class="card">
    <div class="wscale"><div></div><div>${[0, 0.25, 0.5, 0.75, 1].map(p => `<span>${f(wMax * p * 100, 0)}%</span>`).join('')}</div><div></div></div>
    ${wrows}
    <div class="legend" style="margin-top:10px"><span><i style="background:var(--ink);border-radius:50%"></i>통합 가중치</span><span><i style="background:var(--accent-soft);border:1px solid #b9cbf6"></i>개인 가중치 사분위 범위(Q1~Q3)</span><span><i style="background:#5876c9;width:2px"></i>개인 중앙값</span><span><i style="background:#b8c2d3;height:2px"></i>최소~최대 (전원)</span></div>
  </div>
  <div style="margin-top:12px">${tbl('r2w', cmpCols, wcmp, { file: '2차_2부_가중치_비교' })}</div>

  ${sec('2차 3부 · 후보 서비스 평가', `서비스 ${M.svcs.length}개 × 4개 기준 · 가중 종합 = Σ(기준별 평균 × CR≤0.1 통합 가중치)`)}
  ${tbl('r2svc', svCols, svRows, { tools: svTools, file: '2차_3부_서비스_순위', maxh: 720 })}
  <div class="grid g2" style="margin-top:14px">
    <div class="card"><h3>유형별 평균 가중 종합점수</h3><p class="sub">유형 안의 서비스 점수 평균</p>${hbars(typeRows.map(t => ({ label: `${t.type} (${t.cnt})`, v: t.avg, min: 1 })), 5)}</div>
    <div class="card"><h3>기준별 상위 서비스</h3><p class="sub">각 기준 평균 1위</p>${R2.map((id, k) => { const b = r2.ranked.slice().sort((a, c) => (c.crit[k].mean || 0) - (a.crit[k].mean || 0))[0]; return b ? `<div class="op"><div class="who">${esc(M.crit2[k].name)}</div><div class="txt"><b>${esc(b.name)}</b> <span class="mute">${f(b.crit[k].mean)}</span></div></div>` : ''; }).join('')}</div>
  </div>`;
}

/* 3차 */
function vR3() {
  const M = S.M, r2 = M.r2, r3 = M.r3;
  const tot = r3.status.length, sub = r3.subIds.size;
  const svcTypesAll = Array.from(new Set(M.svcs.map(s => s.type)));
  const st3 = S.filt.svcType3 || 'all';
  const ahp3 = S.filt.ahp3 || 'ok';
  const G = ahp3 === 'all' ? r3.gAll : r3.gOk;
  const Wsel = (G && G.w) || r3.W;
  const crPass = r3.indiv.length ? r3.okSet.length / r3.indiv.length * 100 : null;
  const wMax = Math.max(0.4, Math.ceil(Math.max(...r3.wDist.map(d => d.max || 0), ...(Wsel || [0]), ...r2.W) * 10) / 10);
  const wrows = R3.map((id, k) => {
    const d = r3.wDist[k]; const sc = v => (v / wMax * 100);
    return `<div class="wrow"><div class="nm">${esc(M.crit2[k].name)}<small>개인 가중치 중앙값 ${d.n ? f(d.med * 100, 1) + '%' : '-'} · 범위 ${d.n ? f(d.min * 100, 0) + '~' + f(d.max * 100, 0) + '%' : '-'}</small></div>
      <div class="wtrack"><div class="axis"></div>${d.n ? `<div class="wh" style="left:${sc(d.min)}%;width:${sc(d.max - d.min)}%"></div><div class="box" style="left:${sc(d.q1)}%;width:${Math.max(0.5, sc(d.q3 - d.q1))}%"></div><div class="med" style="left:${sc(d.med)}%"></div>` : ''}${Wsel ? `<div class="grp" style="left:${sc(Wsel[k])}%" title="3차 통합 가중치"></div>` : ''}<div class="grp" style="left:${sc(r2.W[k])}%;background:var(--accent);opacity:.55;width:12px;height:12px;margin-left:-6px;top:7px" title="2차 통합 가중치(참고)"></div></div>
      <div class="v">${Wsel ? f(Wsel[k] * 100, 1) + '%' : '-'}</div></div>`;
  }).join('');
  const ahpTools = `<div class="seg">${[['ok', `CR ≤ 0.1 (${r3.okSet.length}명)`], ['all', `전원 (${r3.indiv.length}명)`]].map(([k, l]) => `<button data-filt="ahp3|${k}" class="${ahp3 === k ? 'cur' : ''}">${l}</button>`).join('')}</div>`;
  const wcmp = R3.map((id, k) => ({ name: M.crit2[k].name, w2: r2.W[k] * 100, w3: r3.W[k] * 100, d: (r3.W[k] - r2.W[k]) * 100 }));
  const wcmpCols = [{ k: 'name', l: '평가항목', strong: 1 }, { k: 'w2', l: '2차 가중치', n: 1, fmt: x => f(x, 1) + '%' }, { k: 'w3', l: '3차 가중치', n: 1, fmt: x => f(x, 1) + '%' }, { k: 'd', l: '변화', n: 1, fmt: x => x > 1e-9 ? `<span style="color:var(--ok)">▲${f(x, 1)}%p</span>` : x < -1e-9 ? `<span style="color:var(--bad)">▼${f(-x, 1)}%p</span>` : '-' }];
  const svRows = r3.ranked.filter(s => st3 === 'all' || s.type === st3).map(s => ({ ...s, c0: s.crit[0].mean, c1: s.crit[1].mean, c2: s.crit[2].mean, c3: s.crit[3].mean, wpos: s.wd.posPct, wcons: s.wd.consensus, wconv: s.wd.convergence, wcv: s.wd.cv, nn: s.notes.length }));
  const svCols = [
    { k: 'rank', l: '순위', n: 1 }, { k: 'id', l: 'ID' }, { k: 'name', l: '서비스명', strong: 1 }, { k: 'type', l: '유형', fmt: x => `<span class="mute">${esc(x)}</span>` },
    { k: 'weighted', l: '가중 종합', n: 1, fmt: x => `<b>${f(x)}</b>` }, { k: 'simple', l: '단순 평균', n: 1, fmt: x => f(x) },
    ...R3.map((id, k) => ({ k: 'c' + k, l: id.slice(-1) + ' ' + M.crit2[k].name.split(' ')[0], t: M.crit2[k].name, n: 1, fmt: x => f(x) })),
    { k: 'wpos', l: '4점 이상', n: 1, fmt: x => pc(x, 0) },
    { k: 'wcons', l: '합의도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x >= TH.consensus - 1e-9)}`, csv: x => f(x) },
    { k: 'wconv', l: '수렴도', n: 1, fmt: x => `${f(x)} ${chipPass(x == null ? null : x <= TH.convergence + 1e-9)}`, csv: x => f(x) },
    { k: 'wcv', l: '변이계수', n: 1, fmt: x => f(x) }, { k: 'n', l: 'N', n: 1 }, { k: 'nn', l: '의견', n: 1 }
  ];
  const svTools = `<select class="btn" data-sel="svcType3"><option value="all">유형 전체</option>${svcTypesAll.map(t => `<option value="${esc(t)}" ${t === st3 ? 'selected' : ''}>${esc(t)}</option>`).join('')}</select>`;
  const rk2 = {}; r2.ranked.forEach(s => { rk2[s.id] = s; });
  const mv = r3.ranked.map(s => ({ rank: s.rank, name: s.name, w3: s.weighted, r2rank: rk2[s.id] ? rk2[s.id].rank : null, w2: rk2[s.id] ? rk2[s.id].weighted : null, mv: rk2[s.id] ? rk2[s.id].rank - s.rank : null }));
  const mvCols = [{ k: 'rank', l: '3차 순위', n: 1 }, { k: 'name', l: '서비스명', strong: 1 }, { k: 'w3', l: '3차 가중 종합', n: 1, fmt: x => f(x) }, { k: 'r2rank', l: '2차 순위', n: 1 }, { k: 'w2', l: '2차 가중 종합', n: 1, fmt: x => f(x) }, { k: 'mv', l: '순위 변동', n: 1, fmt: x => x == null ? '-' : x > 0 ? `<span style="color:var(--ok)">▲${x}</span>` : x < 0 ? `<span style="color:var(--bad)">▼${-x}</span>` : '-' }];
  return `
  ${sec('3차 조사 현황', `제출 완료 ${sub}/${tot}명 · 2차와 동일한 4개 평가항목으로 가중치·서비스 점수를 재평가합니다`)}

  ${sec('3차 · 평가항목 가중치 (AHP 쌍대비교)', `응답 ${r3.indiv.length}명 중 일관성 CR ≤ 0.1 충족 ${r3.okSet.length}명 (${pc(crPass)})${G ? ` · 통합 행렬 CR ${f(G.CR, 3)}` : ''}`, ahpTools)}
  <div class="card">
    <div class="wscale"><div></div><div>${[0, 0.25, 0.5, 0.75, 1].map(p => `<span>${f(wMax * p * 100, 0)}%</span>`).join('')}</div><div></div></div>
    ${wrows}
    <div class="legend" style="margin-top:10px"><span><i style="background:var(--ink);border-radius:50%"></i>3차 통합 가중치</span><span><i style="background:var(--accent);border-radius:50%;opacity:.55"></i>2차 통합 가중치(참고)</span><span><i style="background:var(--accent-soft);border:1px solid #b9cbf6"></i>개인 사분위 범위(Q1~Q3)</span></div>
  </div>
  <div style="margin-top:12px">${tbl('r3w', wcmpCols, wcmp, { file: '3차_가중치_비교' })}</div>

  ${sec('3차 · 후보 서비스 평가', `서비스 ${M.svcs.length}개 × 4개 기준 · 제출 완료 ${sub}명 기준`)}
  ${sub ? tbl('r3svc', svCols, svRows, { tools: svTools, file: '3차_서비스_순위', maxh: 720 }) : '<div class="empty">아직 제출된 3차 응답이 없습니다.</div>'}

  ${sec('2차 → 3차 서비스 순위 변동', '2차 가중 종합 순위와 비교한 변화입니다.')}
  ${sub ? tbl('r3mv', mvCols, mv, { file: '2차3차_순위변동', maxh: 720 }) : '<div class="empty">아직 제출된 3차 응답이 없습니다.</div>'}
  <div class="foot-note">3차는 2차와 같은 4개 평가항목의 가중치(AHP)와 서비스 점수만 다시 묻습니다. 1부 적절성 재평가(1~5점)는 3차에 포함되지 않아 항목별 평균·변이계수 비교는 제공하지 않습니다.</div>`;
}

/* 의견 */
function vOpinions() {
  const M = S.M, r2 = M.r2;
  const p1 = r2.p1.map(r => ({ id: r['번호'], note: String(r['보완 의견'] || '').trim(), reasons: R2.map((id, k) => [M.crit2[k].name, String(r[id + '_이유'] || '').trim()]).filter(x => x[1]) })).filter(x => x.note || x.reasons.length);
  const opSvc = S.filt.opSvc;
  const svcWith = r2.services.filter(s => s.notes.length);
  const shown = svcWith.filter(s => opSvc === 'all' || s.id === opSvc);
  return `
  ${sec('2차 1부 · 평가항목 보완 의견', `${p1.length}건 · 제출 완료 응답만`)}
  <div class="card">${p1.length ? p1.map(o => `<div class="op"><div class="who">${who(o.id, true)}</div>${o.note ? `<div class="txt">${esc(o.note)}</div>` : ''}${o.reasons.map(([n, t]) => `<div class="txt"><span class="mute">[${esc(n)}]</span> ${esc(t)}</div>`).join('')}</div>`).join('') : '<div class="empty">의견이 없습니다.</div>'}</div>
  ${sec('2차 3부 · 서비스별 의견', `${svcWith.reduce((a, s) => a + s.notes.length, 0)}건 · 서비스 ${svcWith.length}개`, `<select class="btn" data-sel="opSvc"><option value="all">서비스 전체</option>${svcWith.map(s => `<option value="${esc(s.id)}" ${s.id === opSvc ? 'selected' : ''}>${esc(s.id)} ${esc(s.name)} (${s.notes.length})</option>`).join('')}</select>`)}
  ${shown.map(s => `<div class="card" style="margin-bottom:12px"><h3>${esc(s.id)} · ${esc(s.name)}</h3><p class="sub">${esc(s.type)} · 가중 종합 ${f(s.weighted)} · ${s.rank ? s.rank + '위' : ''}</p>${s.notes.map(n => `<div class="op"><div class="who">${who(n.id, true)}</div><div class="txt">${esc(n.txt)}</div></div>`).join('')}</div>`).join('') || '<div class="empty">의견이 없습니다.</div>'}
  ${M.r3.status.length ? `
  ${sec('3차 · 서비스별 의견', `${M.r3.ranked.reduce((a, s) => a + (s.notes ? s.notes.length : 0), 0)}건`)}
  ${M.r3.ranked.filter(s => s.notes && s.notes.length).map(s => `<div class="card" style="margin-bottom:12px"><h3>${esc(s.id)} · ${esc(s.name)}</h3><p class="sub">${esc(s.type)} · 가중 종합 ${f(s.weighted)} · ${s.rank ? s.rank + '위' : ''}</p>${s.notes.map(n => `<div class="op"><div class="who">${who(n.id, true)}</div><div class="txt">${esc(n.txt)}</div></div>`).join('')}</div>`).join('') || '<div class="empty">의견이 없습니다.</div>'}` : ''}`;
}

/* 품질 */
function vQuality() {
  const M = S.M, r2 = M.r2;
  const hi = r2.indiv.filter(x => x.CR > TH.cr + 1e-9).sort((a, b) => b.CR - a.CR);
  const hiCols = [{ k: 'id', l: '번호' }, { k: 'nm', l: '성명', fmt: (x, r) => S.hide ? '<span class="mute">가림</span>' : esc((M.names[r.id] || {}).name || '') }, { k: 'CR', l: 'CR', n: 1, fmt: x => f(x, 3) }, ...R2.map((id, k) => ({ k: 'w' + k, l: 'w ' + id.slice(-1), n: 1, fmt: x => f(x * 100, 1) + '%' }))];
  const hiRows = hi.map(x => ({ id: x.id, CR: x.CR, w0: x.w[0], w1: x.w[1], w2: x.w[2], w3: x.w[3] }));
  const testRows = (table('status') || []).filter(r => isTest(r['번호']));
  return `
  ${sec('집계 기준과 제외 내역')}
  <div class="card"><dl class="kv">
    <dt>2차 집계 대상</dt><dd>응답_현황 탭 상태가 「제출 완료」인 응답 ${r2.subIds.size}명 (1부 ${r2.p1.length} · 2부 ${r2.p2.length} · 3부 행 ${r2.p3.length})</dd>
    <dt>시험 계정</dt><dd>${testRows.length}개 제외 (${testRows.map(r => esc(r['번호'])).join(', ')})</dd>
    <dt>제출 표시 없는 결과 행</dt><dd>${r2.orphan.length ? r2.orphan.map(o => `${esc(o.id)} (${Object.entries(o.parts).map(([k, v]) => k + ' ' + v + '행').join(', ')}) · 집계 제외 · 연구진 확인 필요`).join('<br>') : '없음'}</dd>
    <dt>제출했는데 결과 행 누락</dt><dd>${r2.missing.length ? r2.missing.map(esc).join(', ') : '없음'}</dd>
    <dt>1차 통계 제외</dt><dd>${CFG.r1Exclude.length ? CFG.r1Exclude.map(esc).join(', ') + ' (1차 마감 뒤 도착)' : '없음'}</dd>
    <dt>CR 재계산 대조</dt><dd>${r2.crMismatch.length ? `시트 값과 다른 응답 ${r2.crMismatch.length}건: ${r2.crMismatch.map(x => esc(x.id)).join(', ')}` : `${r2.indiv.length}건 모두 시트 CR과 일치 (화면에서 쌍대비교 값으로 다시 계산해 대조)`}</dd>
  </dl></div>
  ${sec('2부 일관성 미충족 (CR > 0.1)', `${hi.length}명 · 설문은 확인 후 제출을 허용했음 · 통합 가중치(기본)에서 제외`)}
  ${tbl('crhi', hiCols, hiRows, { file: '2차_CR초과' })}
  ${sec('3부 같은 점수 일괄 응답 의심', '40개 서비스 × 4개 기준(160칸)에 모두 같은 점수를 준 응답')}
  <div class="card">${r2.straight.length ? r2.straight.map(s => `<div class="op"><div class="who">${who(s.id, true)}</div><div class="txt">모든 칸 ${s.v}점</div></div>`).join('') : '<div class="empty">해당 응답 없음</div>'}</div>
  ${sec('명단 비고 (운영 시트 1차_명단)')}
  <div class="card">${M.rosterNotes.map(n => `<div class="op"><div class="who">${who(n.id)}</div><div class="txt">${esc(n.note)}</div></div>`).join('')}</div>
  <div class="foot-note">응답 순서(1부→2부→3부) 위반 여부는 시트에 남지 않아 이 화면에서 판별하지 않습니다. 11/19 확인분: R076(1·2부 완료 전 3부 시작 후 제출), R098(미제출).</div>
  ${M.r3.indiv.length ? `
  ${sec('3차 · 일관성 미충족 (CR > 0.1)', `${M.r3.indiv.filter(x => x.CR > TH.cr + 1e-9).length}명 · 통합 가중치(기본)에서 제외`)}
  <div class="card">${(() => { const hi3 = M.r3.indiv.filter(x => x.CR > TH.cr + 1e-9).sort((a, b) => b.CR - a.CR); return hi3.length ? hi3.map(x => `<div class="op"><div class="who">${who(x.id, true)}</div><div class="txt">CR ${f(x.CR, 3)}</div></div>`).join('') : '해당 응답 없음'; })()}</div>
  ${sec('3차 서비스 일괄 응답 의심', '40개 서비스 × 4개 기준(160칸)에 모두 같은 점수를 준 응답')}
  <div class="card">${M.r3.straight.length ? M.r3.straight.map(s => `<div class="op"><div class="who">${who(s.id, true)}</div><div class="txt">모든 칸 ${s.v}점</div></div>`).join('') : '<div class="empty">해당 응답 없음</div>'}</div>` : ''}`;
}

/* 산식 */
function vMethod() {
  return `${sec('산식과 판정 기준', '연구진 협의로 기준값을 바꿀 수 있습니다.')}
  <div class="card method">
    <h4>공통 (5점 척도 항목)</h4>
    <ul>
      <li>평균, 표준편차(표본, n-1), 중앙값, 사분위수 Q1·Q3(엑셀 QUARTILE.INC와 같은 선형보간)</li>
      <li><b>CVR</b> = (n<sub>e</sub> − N/2) / (N/2), n<sub>e</sub> = 4점·5점 응답 수. 기준값은 응답자 수 N에 따라 이항분포(p=0.5) 단측 유의수준 .05의 정확검정으로 구함(Ayre & Scally, 2014 방식). 예: N=40이면 0.300.</li>
      <li><b>합의도</b> = 1 − (Q3 − Q1) / 중앙값, 기준 ≥ ${TH.consensus}</li>
      <li><b>수렴도</b> = (Q3 − Q1) / 2, 기준 ≤ ${TH.convergence}</li>
      <li><b>변이계수</b> = 표준편차 / 평균, 기준 ≤ ${TH.cv} (차수 간 변화가 작을수록 안정)</li>
    </ul>
    <h4>2부 가중치 (AHP)</h4>
    <ul>
      <li>개인별 4×4 쌍대비교 행렬의 주 고유벡터로 가중치, λmax로 CI = (λmax − n)/(n − 1), CR = CI / RI (RI = 0.90, n=4)</li>
      <li>통합 가중치(기본): CR ≤ 0.1 응답자의 판단값을 칸마다 기하평균(AIJ)한 행렬의 고유벡터. 비교용으로 전원 AIJ, 개인 가중치 기하평균(AIP), 개인 중앙값도 표시</li>
    </ul>
    <h4>3부 서비스 점수</h4>
    <ul>
      <li>기준별 평균 = 서비스마다 4개 기준 점수의 평균</li>
      <li>가중 종합 = Σ(기준별 평균 × 통합 가중치), 단순 평균 = 4개 기준 평균의 평균</li>
      <li>합의도·수렴도·변이계수·4점 이상 비율은 응답자별 가중점수(Σ 점수 × 통합 가중치)로 계산</li>
    </ul>
    <h4>자료 범위</h4>
    <ul>
      <li>서버는 운영 시트를 읽기 전용 권한으로 읽습니다. 휴대폰 뒷자리와 접속키 열은 서버에서 보내지 않습니다.</li>
      <li>2차 결과는 응답_현황 탭 상태가 「제출 완료」인 응답만 씁니다. 작성 중 저장분은 쓰지 않습니다.</li>
      <li>1차 결과는 1차_명단 탭의 A~F 점수(1~5)를 씁니다.</li>
      <li>3차 결과는 3차 전용 설문·운영 시트에서 제출 완료 응답만 씁니다. 3차는 2차와 같은 4개 평가항목의 가중치(AHP)와 서비스 점수만 재평가하며, 1부 적절성 재평가는 포함하지 않습니다.</li>
    </ul>
  </div>`;
}

/* ---------- 이벤트 ---------- */
document.addEventListener('click', e => {
  const t = e.target.closest('[data-tab],[data-act],[data-sort],[data-csv],[data-filt]');
  if (!t) return;
  if (t.dataset.tab) { S.tab = t.dataset.tab; history.replaceState(null, '', '#' + S.tab); render(); window.scrollTo({ top: 0 }); return; }
  if (t.dataset.sort) { const [id, k] = t.dataset.sort.split('|'); const cur = S.sort[id]; S.sort[id] = { k, d: cur && cur.k === k ? -cur.d : (['name', 'id', '번호', '성명', '소속', '상태', 'type'].includes(k) ? 1 : -1) }; render(); return; }
  if (t.dataset.filt) { const [k, v] = t.dataset.filt.split('|'); S.filt[k] = v; render(); return; }
  if (t.dataset.csv) return downloadCsv(t.dataset.csv);
  const a = t.dataset.act;
  if (a === 'reload') load(true);
  if (a === 'auto') { S.auto = !S.auto; localStorage.setItem('aicity_dash_auto', S.auto ? '1' : '0'); schedule(); render(); }
  if (a === 'hide') { S.hide = !S.hide; localStorage.setItem('aicity_dash_hide', S.hide ? '1' : '0'); render(); }
  if (a === 'print') { S.printing = true; render(); setTimeout(() => window.print(), 60); }
  if (a === 'logout') { sessionStorage.removeItem(KEY); localStorage.removeItem(KEY); S.code = ''; S.M = null; S.raw = null; render(); }
});
document.addEventListener('change', e => { const t = e.target.closest('[data-sel]'); if (!t) return; S.filt[t.dataset.sel] = t.value; render(); });
window.addEventListener('afterprint', () => { if (S.printing) { S.printing = false; render(); } });
window.addEventListener('hashchange', () => { const h = location.hash.slice(1); if (h && h !== S.tab && TABS.some(x => x[0] === h)) { S.tab = h; render(); } });
function downloadCsv(id) {
  const t = S.csv[id]; if (!t) return;
  const cell = v => { const s = v == null ? '' : String(v); return /[",\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  const strip = s => String(s).replace(/<[^>]+>/g, '').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&#39;/g, "'").trim();
  const lines = [t.cols.map(c => cell(c.l)).join(',')].concat(t.rows.map(r => t.cols.map(c => cell(c.csv ? c.csv(r[c.k], r) : c.fmt ? strip(c.fmt(r[c.k], r)) : r[c.k])).join(',')));
  const stamp = S.M ? String(S.M.generatedAt).replace(/[^0-9]/g, '').slice(0, 12) : '';
  const blob = new Blob(['\ufeff' + lines.join('\r\n')], { type: 'text/csv;charset=utf-8' });
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = `${t.name}_${stamp}.csv`; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500);
}

/* 시작 */
if (S.code || LOCAL) load(); else render();
schedule();
window.__dash = S;
})();
