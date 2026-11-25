'use strict';
const E=require('../engine.js');
const S=E.S;const {lay,byId,GEN,routeAll}=E;
/* ===== paste from here ===== */
const GXL=110,GXN=160,GXG=200,GXR=260,GYL=130;
function tidy(){
const sh=S.shapes;if(!sh.length)return;
const ids=sh.map(s=>s.id),W=id=>lay(byId(id)).w,H=id=>lay(byId(id)).h;
const isNote=id=>byId(id).kind==='note';
const ed=S.edges.filter(e=>e.from.id!==e.to.id&&byId(e.from.id)&&byId(e.to.id));
const mp=()=>new Map(ids.map(i=>[i,[]]));
const genUp=mp(),genDown=mp(),partUp=mp(),partDown=mp(),deg=new Map(ids.map(i=>[i,0]));
const soft=mp(); /* candidate parents for loosely linked boxes */
for(const e of ed){const a=e.from.id,b=e.to.id;deg.set(a,deg.get(a)+1);deg.set(b,deg.get(b)+1);
if(GEN.has(e.type)){genUp.get(a).push(b);genDown.get(b).push(a);}
else if(e.type==='agg'||e.type==='comp'){partUp.get(b).push({id:a,t:e.type});partDown.get(a).push(b);}
else if(e.type==='note'){soft.get(a).push(b);}
else if(e.type==='directed'||e.type==='depend'){soft.get(b).push(a);}
else{soft.get(a).push(b);soft.get(b).push(a);}}
/* ---- tree parents ---- */
const tp=new Map(),grp=new Map(),sat=new Set();
const anc=(n,x)=>{for(let c=x,k=0;c&&k<999;c=tp.get(c),k++)if(c===n)return true;return false;};
const setP=(n,p,g,s)=>{if(p===n||anc(n,p))return false;tp.set(n,p);grp.set(n,g);if(s)sat.add(n);return true;};
const lone=p=>genDown.get(p).length===1&&genUp.get(p).length===0;
const iso=ids.filter(i=>deg.get(i)===0),isoSet=new Set(iso),bottom=[];
for(const n of ids){const c=genUp.get(n).filter(p=>!lone(p)).sort((a,b)=>genDown.get(b).length-genDown.get(a).length);for(const p of c)if(setP(n,p,0))break;}
for(const n of ids){if(tp.has(n))continue;const c=partUp.get(n).slice().sort((a,b)=>(a.t==='comp'?0:1)-(b.t==='comp'?0:1));for(const q of c)if(setP(n,q.id,1))break;}
for(const n of ids){if(tp.has(n)||isoSet.has(n))continue;if(genUp.get(n).length&&!partUp.get(n).length&&!soft.get(n).length&&genUp.get(n).every(lone))continue;
const c=soft.get(n).filter(x=>!isNote(x)||isNote(n)).sort((a,b)=>deg.get(b)-deg.get(a));for(const p of c)if(setP(n,p,isNote(n)?3:2))break;}
for(const n of ids)for(const p of genUp.get(n)){if(!lone(p)||tp.has(p)&&tp.get(p)!==n)continue;
if(tp.has(n)){if(!tp.has(p))setP(p,n,0,true);}else setP(n,p,0);}
for(const n of iso){const re=new RegExp('\\b'+byId(n).name.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')+'\\b');
const h=ids.find(o=>o!==n&&!isNote(o)&&re.test(byId(o).attrs));if(!(h&&setP(n,h,2)))bottom.push(n);}
const roots=ids.filter(i=>!tp.has(i)&&!bottom.includes(i));
const kids=new Map(ids.map(i=>[i,[]]));for(const [n,p] of tp)kids.get(p).push(n);
/* ---- layers ---- */
const L=new Map(),order=[];const walk=n=>{order.push(n);for(const c of kids.get(n))walk(c);};roots.forEach(walk);
const preds=new Map(ids.map(i=>[i,[]])),succ=new Map(ids.map(i=>[i,[]]));
for(const e of ed){let a,b;if(GEN.has(e.type)){a=e.to.id;b=e.from.id;}else if(e.type==='agg'||e.type==='comp'){a=e.from.id;b=e.to.id;}else continue;
if(sat.has(a)&&tp.get(a)===b)continue;preds.get(b).push(a);succ.get(a).push(b);}
roots.forEach(r=>L.set(r,0));
for(let it=0;it<12;it++){let ch=false;
for(const n of order){let v;if(!tp.has(n))v=L.get(n)||0;else v=sat.has(n)?L.get(tp.get(n)):L.get(tp.get(n))+1;
for(const q of preds.get(n))v=Math.max(v,(L.get(q)||0)+1);if(!tp.has(n)||sat.has(n)){}if(v!==L.get(n)&&(v>(L.get(n)||0)||sat.has(n))){L.set(n,v);ch=true;}}
for(const r of roots){const s=succ.get(r).concat(kids.get(r).filter(c=>!sat.has(c)));if(s.length){const v=Math.min(...s.map(x=>L.get(x)||0))-1;if(v>L.get(r)){L.set(r,v);ch=true;}}}
if(!ch)break;}
const mn=Math.min(...[...L.values()]);for(const [k,v] of L)L.set(k,v-mn);
let nL=0,rowH=[];const rowY=[];
function rows(){nL=Math.max(...ids.filter(i=>!bottom.includes(i)).map(i=>L.get(i)),-1)+1;rowH=Array(nL+1).fill(0);rowY.length=0;
for(const n of ids)if(!bottom.includes(n))rowH[L.get(n)]=Math.max(rowH[L.get(n)],H(n));
let y=0;for(let i=0;i<nL;i++){rowY.push(y);y+=rowH[i]+GYL;}
if(bottom.length){for(const i of bottom){L.set(i,nL);rowH[nL]=Math.max(rowH[nL],H(i));}rowY.push(y);}}
rows();
/* ---- groups ---- */
const G=new Map(),SAT=new Map(),satL=new Map();
for(const n of ids){const g=[[],[],[],[]],sa=[];for(const c of kids.get(n)){if(sat.has(c))sa.push(c);else g[grp.get(c)].push(c);}
G.set(n,g.map((ids_,k)=>({k,ids:ids_})).filter(x=>x.ids.length));SAT.set(n,sa);satL.set(n,false);}
G.set('#',[{k:-1,ids:roots.slice()}]);SAT.set('#',[]);satL.set('#',false);
const mainK=n=>{const g=G.get(n);return g.length?Math.min(...g.map(x=>x.k)):0;};
/* ---- pack ---- */
let rootLeft=false;const ext=new Map(),off=new Map(),leaf=n=>!kids.get(n).length;
function pack(n){const v=n==='#',w=v?0:W(n);const gs=G.get(n);let l=-w/2,r=w/2;
if(!gs.length&&!SAT.get(n).length){ext.set(n,[l,r]);return;}
let cur=0,prev=null,pg=-1,A=Infinity,B=-Infinity;const pos=new Map(),mk=mainK(n);
gs.forEach((g,gi)=>{for(const c of g.ids){pack(c);const [cl,cr]=ext.get(c);
if(prev!==null)cur+=v?GXR:gi!==pg?GXG:(leaf(prev)&&leaf(c)?GXL:GXN);
const x=cur-cl;pos.set(c,x);cur=x+cr;prev=c;pg=gi;if(g.k===mk){A=Math.min(A,x);B=Math.max(B,x);}}});
let mid=gs.length?(A+B)/2:0;if(rootLeft&&!v&&!tp.has(n)&&gs.length){const f=gs[0].ids[0];mid=pos.get(f)+ext.get(f)[0]+w/2;}
for(const [c,x] of pos){const o=x-mid;off.set(c,o);const [cl,cr]=ext.get(c);l=Math.min(l,cl+o);r=Math.max(r,cr+o);}
let lo=l,hi=r;const own=[-w/2,w/2];
for(const s of SAT.get(n)){pack(s);const [sl,sr]=ext.get(s);if(satL.get(n)){const o=lo-GXL-sr;off.set(s,o);lo=o+sl;}else{const o=Math.max(hi,own[1])+GXL-sl;off.set(s,o);hi=o+sr;}
l=Math.min(l,lo);r=Math.max(r,hi);}
ext.set(n,[l,r]);}
const X=new Map();
function absX(){pack('#');const go=(n,x)=>{X.set(n,x);for(const c of G.get(n).flatMap(g=>g.ids).concat(SAT.get(n)))go(c,x+off.get(c));};
const [l,r]=ext.get('#');for(const c of roots)go(c,off.get(c)-(l+r)/2);
if(bottom.length){let tot=bottom.reduce((a,i)=>a+W(i),0)+GXL*(bottom.length-1),x=-tot/2;for(const i of bottom){X.set(i,x+W(i)/2);x+=W(i)+GXL;}}}
/* a line between rows is a vertical Z (tree-like) when it is inheritance, a tree link, or the boxes overlap sideways; otherwise it leaves sideways and drops into the top of the lower box (one bend) */
const treeE=e=>tp.get(e.from.id)===e.to.id||tp.get(e.to.id)===e.from.id;
const isL=(e,ra,rb)=>{if(GEN.has(e.type)||treeE(e))return false;const o=Math.min(ra.x+ra.w,rb.x+rb.w)-Math.max(ra.x,rb.x);return o<30;};
/* ---- proxy cost: model each line as the orthogonal path the router will most likely pick ---- */
const rect=n=>({x:X.get(n)-W(n)/2,y:rowY[L.get(n)],w:W(n),h:H(n)});
const hz=s=>s.a.y===s.b.y;
const segHit=(s,r)=>{const e=3;if(hz(s))return s.a.y>r.y+e&&s.a.y<r.y+r.h-e&&Math.max(s.a.x,s.b.x)>r.x+e&&Math.min(s.a.x,s.b.x)<r.x+r.w-e;
return s.a.x>r.x+e&&s.a.x<r.x+r.w-e&&Math.max(s.a.y,s.b.y)>r.y+e&&Math.min(s.a.y,s.b.y)<r.y+r.h-e;};
function pairCost(u,v){const uh=hz(u),vh=hz(v);
if(uh!==vh){const Hs=uh?u:v,Vs=uh?v:u,y=Hs.a.y,x=Vs.a.x;
return x>Math.min(Hs.a.x,Hs.b.x)+1&&x<Math.max(Hs.a.x,Hs.b.x)-1&&y>Math.min(Vs.a.y,Vs.b.y)+1&&y<Math.max(Vs.a.y,Vs.b.y)-1?1000:0;}
if(u.tk&&u.tk===v.tk)return 0;
if(uh){if(Math.abs(u.a.y-v.a.y)<6){const o=Math.min(Math.max(u.a.x,u.b.x),Math.max(v.a.x,v.b.x))-Math.max(Math.min(u.a.x,u.b.x),Math.min(v.a.x,v.b.x));return o>1?250:0;}}
else if(Math.abs(u.a.x-v.a.x)<6){const o=Math.min(Math.max(u.a.y,u.b.y),Math.max(v.a.y,v.b.y))-Math.max(Math.min(u.a.y,u.b.y),Math.min(v.a.y,v.b.y));return o>1?250:0;}
return 0;}
function cost(){rows();absX();let c=0;const sg=[],rc=new Map(ids.map(n=>[n,rect(n)]));
for(const e of ed){const a=e.from.id,b=e.to.id;let up=a,lo=b;if(L.get(a)>L.get(b)){up=b;lo=a;}const ru=rc.get(up),rl=rc.get(lo),pts=[];
if(L.get(a)!==L.get(b)&&isL(e,ru,rl)){const r=rl.x+rl.w/2>=ru.x+ru.w/2,p={x:r?ru.x+ru.w:ru.x,y:ru.y+ru.h/2},q={x:rl.x+rl.w/2,y:rl.y};pts.push(p,{x:q.x,y:p.y},q);c+=.3*Math.abs(p.x-q.x)+.1*Math.abs(q.y-p.y)+40;}
else if(L.get(a)!==L.get(b)){const p={x:ru.x+ru.w/2,y:ru.y+ru.h},q={x:rl.x+rl.w/2,y:rl.y},ym=rl.y-GYL/2;
pts.push(p,{x:p.x,y:ym},{x:q.x,y:ym},q);c+=.3*Math.abs(p.x-q.x)+.1*Math.abs(q.y-p.y);}
else{const r=rc.get(b).x>=rc.get(a).x,ra=rc.get(a),rb=rc.get(b);pts.push({x:r?ra.x+ra.w:ra.x,y:ra.y+ra.h/2},{x:r?rb.x:rb.x+rb.w,y:rb.y+rb.h/2});c+=120+.5*Math.abs(pts[0].x-pts[1].x);}
const tk=GEN.has(e.type)?(L.get(a)>L.get(b)?b:a)+'t':null;
for(let i=1;i<pts.length;i++){const s={a:pts[i-1],b:pts[i],e:a+'>'+b,n:[a,b],tk};if(s.a.x===s.b.x&&s.a.y===s.b.y)continue;
if(!(s.a.x===s.b.x||s.a.y===s.b.y))s.b={x:s.b.x,y:s.a.y};
sg.push(s);for(const [n,r] of rc){if(n===a||n===b)continue;if(segHit(s,r))c+=900;}}}
for(let i=0;i<sg.length;i++)for(let j=i+1;j<sg.length;j++){const u=sg[i],v=sg[j];if(u.e===v.e)continue;c+=pairCost(u,v);}
return c;}
/* ---- local search over child order ---- */
const perms=a=>{if(a.length<=1)return[a];const o=[];a.forEach((x,i)=>{for(const p of perms(a.slice(0,i).concat(a.slice(i+1))))o.push([x,...p]);});return o;};
const T0=Date.now(),out=()=>Date.now()-T0>100;
const orderSearch=()=>{let best=cost();
for(let sw=0;sw<6;sw++){let imp=false;
for(const n of ['#',...ids]){if(out())break;const gs=G.get(n);
if(gs.length>1){const orig=gs.slice();let bp=orig;for(const p of perms(orig)){G.set(n,p);const c=cost();if(c<best-.01){best=c;bp=p;imp=true;}}G.set(n,bp);}
for(const g of G.get(n)){if(g.ids.length<2)continue;
for(let i=0;i<g.ids.length;i++){const base=g.ids.slice();let bi=base,bc=best;for(let j=0;j<base.length;j++){const t=base.slice(),[m]=t.splice(i,1);t.splice(j,0,m);g.ids=t;const c=cost();if(c<bc-.01){bc=c;bi=t;}}g.ids=bi;if(bc<best-.01){best=bc;imp=true;}}}
if(SAT.get(n).length){satL.set(n,!satL.get(n));const c=cost();if(c<best-.01){best=c;imp=true;}else satL.set(n,!satL.get(n));}}
if(!imp)break;}
return best;};
/* slide a subtree (or a single box) one row down or up when the modelled lines get better */
const sub=n=>[n,...kids.get(n).flatMap(sub)];
const okc=()=>{for(const n of ids){if(bottom.includes(n))continue;if(tp.has(n)){const d=L.get(n)-L.get(tp.get(n));if(sat.has(n)?d!==0:d<1)return false;}for(const q of preds.get(n))if(L.get(q)>=L.get(n))return false;}return true;};
const layerSearch=()=>{let cur=cost();const leafs=ids.filter(n=>!bottom.includes(n)&&!sat.has(n)&&grp.get(n)>=1&&!kids.get(n).length);
for(let it=0;it<3;it++){let imp=false;
for(const n of leafs){if(out())break;L.set(n,L.get(n)+1);if(okc()){const c=cost();if(c<cur-150){cur=c;imp=true;continue;}}L.set(n,L.get(n)-1);}
if(!imp)break;}return cur;};
orderSearch();layerSearch();{const u=[...new Set(ids.filter(i=>!bottom.includes(i)).map(i=>L.get(i)))].sort((a,b)=>a-b);for(const i of ids)if(!bottom.includes(i))L.set(i,u.indexOf(L.get(i)));}orderSearch();
/* ---- write positions + ports (pMode: per-line override, 1 = drop from the bottom, 2 = leave from the side) ---- */
const pMode=new Map(),yOff=new Map(),pIdx=new Map();
function write(){cost();
for(const n of ids){const s=byId(n);s.x=Math.round(X.get(n)-W(n)/2);s.y=Math.round(rowY[L.get(n)]+(yOff.get(n)||0));}
const rowOf=new Map(ids.map(i=>[i,L.get(i)]));
const C=id=>{const s=byId(id),l=lay(s);return{x:s.x+l.w/2,y:s.y+l.h/2};},slots=new Map();
const push=(id,side,it)=>{const k=id+'|'+side;if(!slots.has(k))slots.set(k,[]);slots.get(k).push(it);};
for(const e of S.edges){const a=e.from.id,b=e.to.id;if(!rowOf.has(a)||!rowOf.has(b))continue;
if(a===b){e.from={id:a,side:1,i:0};e.to={id:a,side:0,i:2};continue;}
const ra=rowOf.get(a),rb=rowOf.get(b),ca=C(a),cb=C(b);let sa,sb;
if(ra!==rb){const A=byId(a),B=byId(b),LA=lay(A),LB=lay(B),up=ra<rb,U=up?A:B,Lw=up?B:A,LU=up?LA:LB,LL=up?LB:LA;
let su=2,sl=0;const pm=pMode.get(e.id)||0;if(pm===2||pm===0&&isL(e,{x:U.x,w:LU.w},{x:Lw.x,w:LL.w})){su=Lw.x+LL.w/2>=U.x+LU.w/2?1:3;}
if(up){sa=su;sb=sl;}else{sa=sl;sb=su;}}else if(cb.x>=ca.x){sa=1;sb=3;}else{sa=3;sb=1;}
e.from={id:a,side:sa,i:1};e.to={id:b,side:sb,i:1};
push(a,sa,{e,end:'from',o:sa%2===0?cb.x:cb.y,tree:false});
push(b,sb,{e,end:'to',o:sb%2===0?ca.x:ca.y,tree:GEN.has(e.type)&&sb===2});}
for(const [k,list] of slots){const p=k.split('|'),side=+p[1],c=C(p[0]),md=side%2===0?c.x:c.y;
const tree=list.filter(t=>t.tree),rest=list.filter(t=>!t.tree).sort((u,v)=>u.o-v.o);
if(tree.length){tree.forEach(t=>{t.e[t.end].i=1;});rest.forEach(t=>{t.e[t.end].i=t.o<md?0:2;});}
else{const n=rest.length;rest.forEach((t,j)=>{t.e[t.end].i=n===1?1:n===2?(j===0?0:2):Math.min(2,Math.floor(j*3/n));});}}
for(const [k,v] of pIdx){const [id,end]=k.split('|'),e=S.edges.find(x=>x.id===id);if(e)e[end].i=v;}
}
/* ---- real-route score: route with the page router and judge the drawing ---- */
let nEv=0;function score(){nEv++;write();const RT=routeAll(null),rs=ids.map(n=>{const s=byId(n),l=lay(s);return{id:n,x:s.x,y:s.y,w:l.w,h:l.h};}),sg=[];let c=0;
for(const e of S.edges){const g=RT.get(e.id);if(!g)continue;c+=25*Math.max(0,g.pts.length-2);
for(let i=1;i<g.pts.length;i++){const a=g.pts[i-1],b=g.pts[i],h=Math.abs(a.y-b.y)<.01;c+=.3*(Math.abs(b.x-a.x)+Math.abs(b.y-a.y));sg.push({a,b,e,h});
for(const r of rs){if(r.id===e.from.id||r.id===e.to.id)continue;
if(h){const ov=Math.min(Math.max(a.x,b.x),r.x+r.w)-Math.max(Math.min(a.x,b.x),r.x);if(ov>1){if(a.y>r.y&&a.y<r.y+r.h)c+=3000;else{const d=Math.min(Math.abs(a.y-r.y),Math.abs(a.y-r.y-r.h));if(d<24)c+=(d<10?2500:400)+.5*ov;}}}
else{const ov=Math.min(Math.max(a.y,b.y),r.y+r.h)-Math.max(Math.min(a.y,b.y),r.y);if(ov>1){if(a.x>r.x&&a.x<r.x+r.w)c+=3000;else{const d=Math.min(Math.abs(a.x-r.x),Math.abs(a.x-r.x-r.w));if(d<24)c+=(d<10?2500:400)+.5*ov;}}}}}}
for(let i=0;i<sg.length;i++)for(let j=i+1;j<sg.length;j++){const u=sg[i],v=sg[j];if(u.e===v.e)continue;
if(u.h!==v.h){const H=u.h?u:v,V=u.h?v:u,y=H.a.y,x=V.a.x;if(x>Math.min(H.a.x,H.b.x)+.5&&x<Math.max(H.a.x,H.b.x)-.5&&y>Math.min(V.a.y,V.b.y)+.5&&y<Math.max(V.a.y,V.b.y)-.5)c+=6000;}
else if(u.h?Math.abs(u.a.y-v.a.y)<10:Math.abs(u.a.x-v.a.x)<10){const k=u.h?'x':'y',o=Math.min(Math.max(u.a[k],u.b[k]),Math.max(v.a[k],v.b[k]))-Math.max(Math.min(u.a[k],u.b[k]),Math.min(v.a[k],v.b[k]));if(o>1&&!(GEN.has(u.e.type)&&GEN.has(v.e.type)))c+=200+o;}}
return c;}
/* ---- hill climb on the real score ---- */
const snap=()=>({L:new Map(L),G:new Map([...G].map(([k,v])=>[k,v.map(g=>({k:g.k,ids:g.ids.slice()}))])),SAT:new Map([...SAT].map(([k,v])=>[k,v.slice()])),sat:new Set(sat),satL:new Map(satL),rl:rootLeft,pm:new Map(pMode),yo:new Map(yOff),pi:new Map(pIdx),tp:new Map(tp),grp:new Map(grp),kids:new Map([...kids].map(([k,v])=>[k,v.slice()]))});
const load=z=>{for(const [k,v] of z.L)L.set(k,v);G.clear();for(const [k,v] of z.G)G.set(k,v.map(g=>({k:g.k,ids:g.ids.slice()})));SAT.clear();for(const [k,v] of z.SAT)SAT.set(k,v.slice());sat.clear();z.sat.forEach(x=>sat.add(x));for(const [k,v] of z.satL)satL.set(k,v);rootLeft=z.rl;pMode.clear();for(const [k,v] of z.pm)pMode.set(k,v);yOff.clear();for(const [k,v] of z.yo)yOff.set(k,v);pIdx.clear();for(const [k,v] of z.pi)pIdx.set(k,v);tp.clear();for(const [k,v] of z.tp)tp.set(k,v);for(const [k,v] of z.grp)grp.set(k,v);for(const [k,v] of z.kids)kids.set(k,v.slice());};
const squash=()=>{const u=[...new Set(ids.filter(i=>!bottom.includes(i)).map(i=>L.get(i)))].sort((a,b)=>a-b);for(const i of ids)if(!bottom.includes(i))L.set(i,u.indexOf(L.get(i)));};
const okL=()=>{for(const n of ids){if(bottom.includes(n))continue;if(tp.has(n)){const d=L.get(n)-L.get(tp.get(n));if(sat.has(n)?d!==0:d<1)return false;}for(const q of preds.get(n))if(!(sat.has(n)&&q===tp.get(n))&&L.get(q)>=L.get(n))return false;}return true;};
const moves=[],fine=[];
for(const n of ids){if(bottom.includes(n)||!tp.has(n)||!leaf(n))continue;
moves.push(()=>{if(sat.has(n))return false;L.set(n,L.get(n)+1);return okL();});
moves.push(()=>{if(sat.has(n))return false;L.set(n,L.get(n)-1);if(!okL())return false;squash();return true;});
if(!GEN.has((ed.find(e=>e.from.id===n&&e.to.id===tp.get(n)||e.to.id===n&&e.from.id===tp.get(n))||{}).type)){const p=tp.get(n);
moves.push(()=>{if(sat.has(n)){sat.delete(n);SAT.set(p,SAT.get(p).filter(x=>x!==n));let g=G.get(p).find(x=>x.k===grp.get(n));if(!g){g={k:grp.get(n),ids:[]};G.get(p).push(g);G.get(p).sort((a,b)=>a.k-b.k);}g.ids.push(n);L.set(n,L.get(p)+1);}
else{sat.add(n);for(const g of G.get(p))g.ids=g.ids.filter(x=>x!==n);G.set(p,G.get(p).filter(g=>g.ids.length));SAT.get(p).push(n);L.set(n,L.get(p));}
if(!okL())return false;squash();return true;});}}
/* drop a box part-way into the gap below its row (moves lines off its top edge) */
for(const n of ids)if(!bottom.includes(n))fine.push(()=>{yOff.set(n,yOff.get(n)?0:Math.round(GYL*.35));return true;});
/* pin one end of a line to another port on its side */
for(const e of S.edges)if(!GEN.has(e.type)&&e.from.id!==e.to.id)for(const end of ['from','to'])for(const v of [0,1,2])fine.push(()=>{const k=e.id+'|'+end;if(pIdx.get(k)===v)return false;pIdx.set(k,v);return true;});
/* re-hang a loose leaf under another box it links to */
for(const n of ids){if(bottom.includes(n)||!tp.has(n)||!leaf(n)||genUp.get(n).length)continue;
const nb=[...new Set(ed.filter(e=>e.from.id===n||e.to.id===n).map(e=>e.from.id===n?e.to.id:e.from.id))].filter(x=>!isNote(x)&&!bottom.includes(x));
for(const q of nb)moves.push(()=>{const p=tp.get(n);if(q===p||sat.has(n)||anc(n,q))return false;
for(const g of G.get(p))g.ids=g.ids.filter(x=>x!==n);G.set(p,G.get(p).filter(g=>g.ids.length));kids.set(p,kids.get(p).filter(x=>x!==n));
tp.set(n,q);grp.set(n,2);kids.get(q).push(n);let g=G.get(q).find(x=>x.k===2);if(!g){g={k:2,ids:[]};G.get(q).push(g);G.get(q).sort((a,b)=>a.k-b.k);}g.ids.push(n);
L.set(n,Math.max(L.get(n),L.get(q)+1));if(!okL())return false;squash();return true;});}
for(const n of ids)moves.push(()=>{if(!SAT.get(n).length)return false;satL.set(n,!satL.get(n));return true;});
for(const n of ['#',...ids])moves.push(()=>{let ch=false;for(const g of G.get(n))if(g.ids.length>1){g.ids.push(g.ids.shift());ch=true;}return ch;},()=>{let ch=false;for(const g of G.get(n))if(g.ids.length>1){g.ids.unshift(g.ids.pop());ch=true;}return ch;},()=>{if(G.get(n).length<2)return false;G.get(n).reverse();return true;});
for(const e of ed)if(!GEN.has(e.type))fine.push(()=>{if(L.get(e.from.id)===L.get(e.to.id)||treeE(e))return false;pMode.set(e.id,((pMode.get(e.id)||0)+1)%3);return true;},()=>{if(L.get(e.from.id)===L.get(e.to.id)||treeE(e))return false;pMode.set(e.id,((pMode.get(e.id)||0)+2)%3);return true;});
if(roots.some(r=>G.get(r).length))moves.push(()=>{rootLeft=!rootLeft;return true;});
{const T1=Date.now(),EVMAX=220;let best=score(),bz=snap();
let cap=EVMAX;const late=()=>nEv>cap||Date.now()-T1>1200;
const climb=(ms=moves)=>{for(let sw=0;sw<4&&!late();sw++){let imp=false;
for(const m of ms){if(late())break;if(m()){const c=score();if(c<best-1){best=c;bz=snap();imp=true;continue;}}load(bz);}
if(!imp)break;}};
climb();
/* pairs of moves, for changes that only pay off together (e.g. drop a box a row and reorder its siblings) */
for(let i=0;i<moves.length&&!late();i++)for(let j=i+1;j<moves.length&&!late();j++){if(moves[i]()&&moves[j]()){const c=score();if(c<best-1){best=c;bz=snap();load(bz);climb();continue;}}load(bz);}
cap=nEv+180;climb(fine);
load(bz);write();}
}
/* ===== to here ===== */
module.exports={tidy};
