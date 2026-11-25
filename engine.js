'use strict';
/* Node harness: functions below are copied verbatim from the artifact's <script>. Only browser bits are shimmed. */
const LH=18,PAD=8,PX=12,G=24,MINW=150,GAPX=100,GAPY=110,MAXROW=5;
const F={disp:"'Space Grotesk', Inter, Arial, sans-serif",text:"Inter, Arial, sans-serif"};
const KINDS={class:{label:'Class',st:''},abstract:{label:'Abstract class',st:'abstract',it:true},interface:{label:'Interface',st:'interface'},enum:{label:'Enum',st:'enumeration'},note:{label:'Note',note:true}};
const RELS=[
{k:'assoc',name:'Association',say:(a,b)=>`${a} is linked to ${b}`},
{k:'directed',name:'Directed association',e:'open',say:(a,b)=>`${a} knows about ${b}`},
{k:'inherit',name:'Inheritance',e:'tri',say:(a,b)=>`${a} extends ${b}`},
{k:'realize',name:'Realization',e:'tri',dash:1,say:(a,b)=>`${a} implements ${b}`},
{k:'depend',name:'Dependency',e:'open',dash:1,say:(a,b)=>`${a} uses ${b}`},
{k:'agg',name:'Aggregation',s:'dia',say:(a,b)=>`${a} has ${b}; parts can outlive it`},
{k:'comp',name:'Composition',s:'diaf',say:(a,b)=>`${a} owns ${b}; parts die with it`},
{k:'note',name:'Note link',dash:1,say:()=>'attaches the note'}];
const REL=Object.fromEntries(RELS.map(r=>[r.k,r]));
const GEN=new Set(['inherit','realize']);
const DARK={ink:'#e6e8ec',mut:'#9aa3b2',paper:'#1b1e24',card:'#23272f',head:'#2c323c',note:'#3a3520',acc:'#4c9dff'};
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
/* shim: text width estimate */
const tw=(t,f)=>String(t).length*(/Space Grotesk/.test(f)?8.8:7.0);
const snap=v=>Math.round(v/10)*10;
const n1=v=>+v.toFixed(1);
/* shim: module-level state (stable object identity so layout modules can hold a reference) */
const S={shapes:[],edges:[],nid:1};
function setS(d){S.shapes=d.shapes;S.edges=d.edges;S.nid=d.nid;}
let sel=null,hover=null,drag=null,pending=null,view={tx:0,ty:0,s:1};
let LC=new WeakMap();
const VIS=['-','#','~','+'],VISNAME={'-':'private','#':'protected','~':'package','+':'public'},VRE=/^\s*([+\-#~])\s*/;
const hv=(sh,f)=>!KINDS[sh.kind].note&&!(sh.kind==='enum'&&f==='attrs');
function mem(t,vis){const out=[];String(t).split('\n').forEach((s,idx)=>{if(!s.trim())return;let u=false,i=false,m=s.match(VRE),v=null;
if(m){s=s.slice(m[0].length);if(vis)v=m[1];}else{s=s.trim();if(vis)v='-';}
while((m=s.match(/^(static|abstract)\s+/))){if(m[1]==='static')u=true;else i=true;s=s.slice(m[0].length);}
out.push({v,t:s.replace(/\s+$/,''),u,i,idx});});return out;}
function norm(sh){for(const f of ['attrs','methods'])if(hv(sh,f))sh[f]=String(sh[f]).split('\n').map(l=>!l.trim()||VRE.test(l)?l:'- '+l.trim()).join('\n');}
const byId=id=>S.shapes.find(s=>s.id===id);
const edgeById=id=>S.edges.find(e=>e.id===id);

function lay(sh){
const key=sh.kind+'\u0001'+sh.name+'\u0001'+sh.attrs+'\u0001'+sh.methods,c=LC.get(sh);if(c&&c.key===key)return c.L;
const L=lay0(sh);LC.set(sh,{key,L});return L;}
function lay0(sh){
const k=KINDS[sh.kind];
if(k.note){const ls=String(sh.attrs).split('\n');const w=Math.max(160,...ls.map(l=>tw(l,`13px ${F.text}`)+PX*2+14));const h=Math.max(60,ls.length*LH+PAD*2+4);const W=Math.ceil(w/10)*10,H=Math.ceil(h/10)*10;return{w:W,h:H,note:true,ls,comps:[{f:'attrs',y:0,h:H}]};}
const st=k.st?`«${k.st}»`:'',hh=PAD*2+(st?LH:0)+20,A=mem(sh.attrs,hv(sh,'attrs')),M=mem(sh.methods,true);
const ah=Math.max(16,A.length*LH+PAD),mh=Math.max(16,M.length*LH+PAD);
const w=Math.ceil(Math.max(MINW,tw(sh.name||' ',`600 15px ${F.disp}`)+PX*2,st?tw(st,`13px ${F.text}`)+PX*2:0,...A.concat(M).map(m=>tw(m.t,`${m.i?'italic ':''}13px ${F.text}`)+PX*2+(m.v?16:0)))/10)*10;
return{w,h:hh+ah+mh,st,hh,ah,mh,A,M,it:!!k.it,comps:[{f:'name',y:0,h:hh},{f:'attrs',y:hh,h:ah},{f:'methods',y:hh+ah,h:mh}]};
}
function port(sh,L,p){const t=(p.i+1)/4;
switch(p.side){case 0:return{x:sh.x+L.w*t,y:sh.y,dx:0,dy:-1};case 1:return{x:sh.x+L.w,y:sh.y+L.h*t,dx:1,dy:0};case 2:return{x:sh.x+L.w*t,y:sh.y+L.h,dx:0,dy:1};default:return{x:sh.x,y:sh.y+L.h*t,dx:-1,dy:0};}}

const eq=(a,b)=>Math.abs(a-b)<.01;
function simp(a){const o=[];for(const p of a){const q=o[o.length-1];if(q&&eq(q.x,p.x)&&eq(q.y,p.y))continue;o.push({x:p.x,y:p.y});}
for(let i=1;i<o.length-1;){const A=o[i-1],B=o[i],C=o[i+1];if((eq(A.x,B.x)&&eq(B.x,C.x))||(eq(A.y,B.y)&&eq(B.y,C.y)))o.splice(i,1);else i++;}return o;}
function hit(a,b,r){const e=1;if(eq(a.y,b.y))return a.y>r.y+e&&a.y<r.y+r.h-e&&Math.max(a.x,b.x)>r.x+e&&Math.min(a.x,b.x)<r.x+r.w-e;
return a.x>r.x+e&&a.x<r.x+r.w-e&&Math.max(a.y,b.y)>r.y+e&&Math.min(a.y,b.y)<r.y+r.h-e;}
function rects(){return S.shapes.map(s=>{const L=lay(s);return{id:s.id,x:s.x,y:s.y,w:L.w,h:L.h};});}
function clash(a,b,used,tk){let s=0;const hz=eq(a.y,b.y);
for(const u of used){if(tk&&u.tk===tk)continue;const c=u.a,d=u.b,uh=eq(c.y,d.y);
if(hz&&uh&&Math.abs(a.y-c.y)<8){const o=Math.min(Math.max(a.x,b.x),Math.max(c.x,d.x))-Math.max(Math.min(a.x,b.x),Math.min(c.x,d.x));if(o>.5)s+=300+o*4;}
else if(!hz&&!uh&&Math.abs(a.x-c.x)<8){const o=Math.min(Math.max(a.y,b.y),Math.max(c.y,d.y))-Math.max(Math.min(a.y,b.y),Math.min(c.y,d.y));if(o>.5)s+=300+o*4;}
else if(hz!==uh){const H=hz?[a,b]:[c,d],V=hz?[c,d]:[a,b];const y=H[0].y,x=V[0].x;
if(x>Math.min(H[0].x,H[1].x)+.5&&x<Math.max(H[0].x,H[1].x)-.5&&y>Math.min(V[0].y,V[1].y)+.5&&y<Math.max(V[0].y,V[1].y)-.5)s+=40;}}
return s;}
function score(raw,pts,p1,p2,ra,rb,obs,used,tk){let s=0;
for(let i=1;i<pts.length;i++){const a=pts[i-1],b=pts[i];s+=Math.abs(b.x-a.x)+Math.abs(b.y-a.y);
for(const o of obs)if(hit(a,b,o))s+=(o.id===ra.id||o.id===rb.id)?3000:1200;
if(used&&used.length)s+=clash(a,b,used,tk);}
s+=(pts.length-2)*20;
const dir=(a,b)=>({x:Math.sign(Math.round(b.x-a.x)),y:Math.sign(Math.round(b.y-a.y))});
for(let i=2;i<raw.length-1;i++){const v=dir(raw[i-1],raw[i]);if(v.x||v.y){if(v.x*p1.dx+v.y*p1.dy<0)s+=1500;break;}}
for(let i=raw.length-3;i>0;i--){const v=dir(raw[i],raw[i+1]);if(v.x||v.y){if(v.x*p2.dx+v.y*p2.dy>0)s+=1500;break;}}
return s;}
function route(p1,p2,ra,rb,used,tk){
const obs=rects(),s1={x:p1.x+p1.dx*G,y:p1.y+p1.dy*G},s2={x:p2.x+p2.dx*G,y:p2.y+p2.dy*G};
const L=Math.min(ra.x,rb.x)-G,R=Math.max(ra.x+ra.w,rb.x+rb.w)+G,T=Math.min(ra.y,rb.y)-G,B=Math.max(ra.y+ra.h,rb.y+rb.h)+G;
const mx=(s1.x+s2.x)/2,my=(s1.y+s2.y)/2;
const C=[[{x:s2.x,y:s1.y}],[{x:s1.x,y:s2.y}]];
const XS=[mx,mx-16,mx+16,mx-32,mx+32,L,L-16,R,R+16],YS=[my,my-16,my+16,my-32,my+32,T,T-16,B,B+16];
if(CORR){const x0=Math.min(s1.x,s2.x)-360,x1=Math.max(s1.x,s2.x)+360,y0=Math.min(s1.y,s2.y)-300,y1=Math.max(s1.y,s2.y)+300;
for(const x of CORR.xs)if(x>x0&&x<x1)XS.push(x,x-14,x+14);for(const y of CORR.ys)if(y>y0&&y<y1)YS.push(y,y-14,y+14);}
for(const x of XS)C.push([{x,y:s1.y},{x,y:s2.y}]);
for(const y of YS)C.push([{x:s1.x,y},{x:s2.x,y}]);
let best=null,bs=Infinity;
for(const c of C){const raw=[p1,s1,...c,s2,p2],pts=simp(raw),sc=score(raw,pts,p1,p2,ra,rb,obs,used,tk);if(sc<bs){bs=sc;best=pts;}}
return best;}
let CORR=null;
function corridors(){const xs=new Set(),ys=new Set();for(const r of rects()){xs.add(Math.round(r.x-GAPX/2));xs.add(Math.round(r.x+r.w+GAPX/2));ys.add(Math.round(r.y-GAPY/2));ys.add(Math.round(r.y+r.h+GAPY/2));}return{xs:[...xs],ys:[...ys]};}
function routeAll(ov){const out=new Map(),used=[];CORR=corridors();
for(const e of S.edges){let a=e.from,b=e.to;
if(ov&&ov.eid===e.id){if(ov.end==='from')a=ov.r;else b=ov.r;}
const tk=GEN.has(e.type)?e.to.id+'|'+e.to.side+'|'+e.to.i:null;
const g=geom(a,b,used,tk);if(!g)continue;out.set(e.id,g);
for(let i=1;i<g.pts.length;i++)used.push({a:g.pts[i-1],b:g.pts[i],tk});}
CORR=null;return out;}
function routeFree(p,c){const s={x:p.x+p.dx*G,y:p.y+p.dy*G};return simp([p,s,p.dx?{x:c.x,y:s.y}:{x:s.x,y:c.y},c]);}
function endInfo(ref){if(!ref||ref.free)return null;const sh=byId(ref.id);if(!sh)return null;const L=lay(sh);return{p:port(sh,L,ref),r:{id:sh.id,x:sh.x,y:sh.y,w:L.w,h:L.h}};}
function geom(a,b,used,tk){const A=endInfo(a),B=endInfo(b);
if(A&&B)return{pts:route(A.p,B.p,A.r,B.r,used,tk),p1:A.p,p2:B.p};
if(A&&b&&b.free)return{pts:routeFree(A.p,b.free),p1:A.p,p2:null};
if(B&&a&&a.free)return{pts:routeFree(B.p,a.free).reverse(),p1:null,p2:B.p};
return null;}
const pd=pts=>'M'+pts.map(p=>n1(p.x)+','+n1(p.y)).join(' L');

function tidy(){
const sh=S.shapes;if(!sh.length)return;
const par=new Map(sh.map(s=>[s.id,[]])),nb=new Map(sh.map(s=>[s.id,new Set()])),inGen=new Set();
for(const e of S.edges){const a=e.from.id,b=e.to.id;if(a===b||!nb.has(a)||!nb.has(b))continue;nb.get(a).add(b);nb.get(b).add(a);if(GEN.has(e.type)){par.get(a).push(b);inGen.add(a);inGen.add(b);}}
const layer=new Map(),vis=new Set();
const depth=id=>{if(layer.has(id))return layer.get(id);if(vis.has(id))return 0;vis.add(id);let d=0;for(const p of par.get(id))d=Math.max(d,depth(p)+1);layer.set(id,d);return d;};
inGen.forEach(depth);
const adj=new Map(sh.map(s=>[s.id,[]]));
for(const e of S.edges){const a=e.from.id,b=e.to.id;if(a===b||!adj.has(a)||!adj.has(b))continue;const d=(e.type==='agg'||e.type==='comp')?1:0;adj.get(a).push([b,d]);adj.get(b).push([a,-d]);}
const spread=q=>{while(q.length){const id=q.shift();for(const [n,d] of adj.get(id))if(!layer.has(n)){layer.set(n,layer.get(id)+d);q.push(n);}}};
spread([...layer.keys()]);
for(const s of sh)if(!layer.has(s.id)){layer.set(s.id,0);spread([s.id]);}
const minL=Math.min(...layer.values());for(const [k,v] of layer)layer.set(k,v-minL);
const iso=sh.filter(s=>nb.get(s.id).size===0);if(iso.length&&iso.length<sh.length){const mx=Math.max(...sh.filter(s=>nb.get(s.id).size).map(s=>layer.get(s.id)));iso.forEach(s=>layer.set(s.id,mx+1));}
const rows=[];for(const s of sh){const l=layer.get(s.id);(rows[l]||(rows[l]=[])).push(s.id);}
const R=rows.filter(Boolean),X=new Map(),W=id=>lay(byId(id)).w,rowI=new Map();
R.forEach((r,i)=>r.forEach(id=>rowI.set(id,i)));
const place=r=>{const tot=r.reduce((a,id)=>a+W(id),0)+GAPX*(r.length-1);let x=-tot/2;for(const id of r){X.set(id,x+W(id)/2);x+=W(id)+GAPX;}};
R.forEach(place);
const E=[];for(const e of S.edges){const a=e.from.id,b=e.to.id;if(a!==b&&rowI.has(a)&&rowI.has(b))E.push([a,b]);}
const GE=new Set();for(const e of S.edges)if(GEN.has(e.type))GE.add(e.from.id+'>'+e.to.id);
const cost=()=>{let c=0;for(const [a,b] of E){const dx=Math.abs(X.get(a)-X.get(b)),w=GE.has(a+'>'+b)?2:1;if(rowI.get(a)===rowI.get(b)){const r=R[rowI.get(a)];c+=dx+(Math.abs(r.indexOf(a)-r.indexOf(b))-1)*400;}else c+=dx*w;}return c;};
const perms=a=>{if(a.length<=1)return[a];const o=[];a.forEach((x,i)=>{for(const p of perms(a.slice(0,i).concat(a.slice(i+1))))o.push([x,...p]);});return o;};
for(let pass=0;pass<3;pass++)for(let ri=0;ri<R.length;ri++){let r=R[ri];if(r.length<2)continue;
if(r.length<=7){let best=r,bc=Infinity;for(const p of perms(r.slice())){R[ri]=p;place(p);const c=cost();if(c<bc-.01){bc=c;best=p;}}R[ri]=best;place(best);}
else{
const bcx=new Map(r.map(id=>{const ns=[...nb.get(id)];return[id,ns.length?ns.reduce((a,n)=>a+X.get(n),0)/ns.length:X.get(id)];}));r=r.slice().sort((a,b)=>bcx.get(a)-bcx.get(b));R[ri]=r;place(r);
let c0=cost();for(let g=0,imp=true;imp&&g<8;g++){imp=false;for(let i=0;i<r.length;i++)for(let j=0;j<r.length;j++){if(i===j)continue;const t=r.slice(),[m]=t.splice(i,1);t.splice(j,0,m);R[ri]=t;place(t);const c=cost();if(c<c0-.01){c0=c;r=t;imp=true;}else{R[ri]=r;place(r);}}}}}
const fin=[];for(const r of R){const k=Math.ceil(r.length/MAXROW),sz=Math.ceil(r.length/k);for(let i=0;i<r.length;i+=sz)fin.push(r.slice(i,i+sz));}
const nbw=new Map(sh.map(s=>[s.id,[]]));
for(const e of S.edges){const a=e.from.id,b=e.to.id;if(a===b||!nbw.has(a)||!nbw.has(b))continue;const w=GEN.has(e.type)?3:1;nbw.get(a).push([b,w]);nbw.get(b).push([a,w]);}
const fr=new Map();fin.forEach((r,i)=>{r.forEach(id=>fr.set(id,i));place(r);});
for(let it=0;it<14;it++){const ord=fin.map((_,i)=>i);if(it%2)ord.reverse();
for(const ri of ord){const r=fin[ri],hw=r.map(id=>W(id)/2);
const d=r.map(id=>{let s=X.get(id)*.6,t=.6;for(const [n,w] of nbw.get(id)){s+=X.get(n)*w;t+=w;}return s/t;});
const f=d.slice();for(let i=1;i<r.length;i++)f[i]=Math.max(f[i],f[i-1]+hw[i-1]+hw[i]+GAPX);
const bk=d.slice();for(let i=r.length-2;i>=0;i--)bk[i]=Math.min(bk[i],bk[i+1]-hw[i+1]-hw[i]-GAPX);
const m=d.map((_,i)=>(f[i]+bk[i])/2);for(let i=1;i<r.length;i++)m[i]=Math.max(m[i],m[i-1]+hw[i-1]+hw[i]+GAPX);
r.forEach((id,i)=>X.set(id,m[i]));}}
const span=r=>r.reduce((a,id)=>a+W(id),0)+GAPX*(r.length-1),cap=Math.max(...fin.map(span))*1.2;
const ext=()=>{let lo=Infinity,hi=-Infinity;for(const r of fin)for(const id of r){lo=Math.min(lo,X.get(id)-W(id)/2);hi=Math.max(hi,X.get(id)+W(id)/2);}return[lo,hi];};
let [lo,hi]=ext();
if(hi-lo>cap){const k=cap/(hi-lo),c=(lo+hi)/2;for(const r of fin){for(const id of r)X.set(id,c+(X.get(id)-c)*k);
for(let i=1;i<r.length;i++){const need=X.get(r[i-1])+W(r[i-1])/2+W(r[i])/2+GAPX;if(X.get(r[i])<need)X.set(r[i],need);}}}
let y=0;const rowOf=new Map();
fin.forEach((r,ri)=>{let mh=0;
for(const id of r){const s=byId(id);s.x=snap(X.get(id)-W(id)/2);s.y=snap(y);mh=Math.max(mh,lay(s).h);rowOf.set(id,ri);}y+=mh+GAPY;});
const C=id=>{const s=byId(id),l=lay(s);return{x:s.x+l.w/2,y:s.y+l.h/2};},slots=new Map();
const push=(id,side,it)=>{const k=id+'|'+side;if(!slots.has(k))slots.set(k,[]);slots.get(k).push(it);};
for(const e of S.edges){const a=e.from.id,b=e.to.id;if(!rowOf.has(a)||!rowOf.has(b))continue;
if(a===b){e.from={id:a,side:1,i:0};e.to={id:a,side:0,i:2};continue;}
const ra=rowOf.get(a),rb=rowOf.get(b),ca=C(a),cb=C(b);let sa,sb;
if(ra!==rb){if(rb<ra){sa=0;sb=2;}else{sa=2;sb=0;}}else if(cb.x>=ca.x){sa=1;sb=3;}else{sa=3;sb=1;}
e.from={id:a,side:sa,i:1};e.to={id:b,side:sb,i:1};
push(a,sa,{e,end:'from',o:sa%2===0?cb.x:cb.y,tree:false});
push(b,sb,{e,end:'to',o:sb%2===0?ca.x:ca.y,tree:GEN.has(e.type)&&sb===2});}
for(const [k,list] of slots){const p=k.split('|'),side=+p[1],c=C(p[0]),md=side%2===0?c.x:c.y;
const tree=list.filter(t=>t.tree),rest=list.filter(t=>!t.tree).sort((u,v)=>u.o-v.o);
if(tree.length){tree.forEach(t=>{t.e[t.end].i=1;});rest.forEach(t=>{t.e[t.end].i=t.o<md?0:2;});}
else{const n=rest.length;rest.forEach((t,j)=>{t.e[t.end].i=n===1?1:n===2?(j===0?0:2):Math.min(2,Math.floor(j*3/n));});}}
}

const KALIAS={class:'class',abstract:'abstract','abstract class':'abstract',interface:'interface',enum:'enum',enumeration:'enum'};
const TALIAS={assoc:'assoc',association:'assoc',directed:'directed','directed association':'directed',inherit:'inherit',inheritance:'inherit',extends:'inherit',generalization:'inherit',realize:'realize',realization:'realize',implements:'realize',depend:'depend',dependency:'depend',uses:'depend',agg:'agg',aggregation:'agg',comp:'comp',composition:'comp'};
function fromSpec(sp){
if(!sp||typeof sp!=='object'||!Array.isArray(sp.classes))return null;
const str=v=>typeof v==='string'?v.slice(0,5000):'',txt=v=>Array.isArray(v)?v.map(x=>str(String(x))).join('\n'):str(v);
const d={shapes:[],edges:[],nid:1},ids=new Map(),id=p=>p+(d.nid++);
const add=(name,kind,attrs,methods)=>{const s={id:id('s'),kind,x:0,y:0,name,attrs,methods};d.shapes.push(s);ids.set(name,s.id);return s;};
for(const c of sp.classes){if(!c)continue;const name=str(c.name).trim().slice(0,120);if(!name||ids.has(name))continue;add(name,KALIAS[String(c.kind||'class').toLowerCase()]||'class',txt(c.attrs),txt(c.methods));}
const ref=n=>{n=str(n).trim().slice(0,120);if(!n)return null;if(!ids.has(n))add(n,'class','','');return{id:ids.get(n),side:0,i:1};};
for(const r of Array.isArray(sp.relations)?sp.relations:[]){if(!r)continue;const t=TALIAS[String(r.type||'assoc').toLowerCase()];if(!t)continue;const f=ref(r.from),to=ref(r.to);if(!f||!to)continue;
d.edges.push({id:id('e'),type:t,from:f,to,label:str(r.label),fromMult:str(r.fromMult),toMult:str(r.toMult)});}
for(const n of Array.isArray(sp.notes)?sp.notes:[]){if(!n)continue;const s={id:id('s'),kind:'note',x:0,y:0,name:'',attrs:txt(n.text)||'Note',methods:''};d.shapes.push(s);
const a=ids.get(str(n.attach).trim());if(a)d.edges.push({id:id('e'),type:'note',from:{id:s.id,side:0,i:1},to:{id:a,side:0,i:1},label:'',fromMult:'',toMult:''});}
d.shapes.forEach(norm);return d;}

function mk(pre,ink,fill){
const m=(id,w,h,rx,ry,body)=>`<marker id="${pre}-${id}" markerUnits="userSpaceOnUse" markerWidth="${w}" markerHeight="${h}" refX="${rx}" refY="${ry}" orient="auto-start-reverse" overflow="visible">${body}</marker>`;
const dia='M1,7 L11,1 L21,7 L11,13 Z';
return m('open',14,14,13,7,`<path d="M1,1 L13,7 L1,13" fill="none" stroke="${ink}" stroke-width="1.5" stroke-linejoin="round" stroke-linecap="round"/>`)
+m('tri',16,18,15,9,`<path d="M1,1 L15,9 L1,17 Z" fill="${fill}" stroke="${ink}" stroke-width="1.5" stroke-linejoin="round"/>`)
+m('dia',22,14,21,7,`<path d="${dia}" fill="${fill}" stroke="${ink}" stroke-width="1.5" stroke-linejoin="round"/>`)
+m('diaf',22,14,21,7,`<path d="${dia}" fill="${ink}" stroke="${ink}" stroke-width="1.5" stroke-linejoin="round"/>`);
}
function mid(pts){const seg=[];let tot=0;for(let i=1;i<pts.length;i++){const l=Math.abs(pts[i].x-pts[i-1].x)+Math.abs(pts[i].y-pts[i-1].y);seg.push(l);tot+=l;}
let h=tot/2;for(let i=1;i<pts.length;i++){const l=seg[i-1];if(h<=l&&l>0){const a=pts[i-1],b=pts[i],t=h/l;return{x:a.x+(b.x-a.x)*t,y:a.y+(b.y-a.y)*t,hz:eq(a.y,b.y)};}h-=l;}return{x:pts[0].x,y:pts[0].y,hz:true};}
function txt(P,x,y,t,a){return`<text x="${n1(x)}" y="${n1(y)}" text-anchor="${a}" font-size="13" font-family="${F.text}" fill="${P.ink}" paint-order="stroke" stroke="${P.paper}" stroke-width="4" stroke-linejoin="round">${esc(t)}</text>`;}
function multAt(P,p,t){if(!p||!t)return'';if(p.dx)return txt(P,p.x+p.dx*8,p.y-12,t,p.dx>0?'start':'end');return txt(P,p.x+10,p.y+(p.dy>0?22:-10),t,'start');}
function edgeSVG(e,g,P,mp,isSel,ui){
const r=REL[e.type]||REL.assoc,col=isSel?P.acc:P.ink,d=pd(g.pts);
let s=`<g${ui?` data-e="${esc(e.id)}"`:''}>`;
if(ui)s+=`<path d="${d}" fill="none" stroke="transparent" stroke-width="14"/>`;
s+=`<path d="${d}" fill="none" stroke="${col}" stroke-width="${isSel?2:1.5}"${r.dash?' stroke-dasharray="7 5"':''}${r.s?` marker-start="url(#${mp}-${r.s})"`:''}${r.e?` marker-end="url(#${mp}-${r.e})"`:''}/>`;
if(e.label){let m=mid(g.pts),best=0;
for(let i=1;i<g.pts.length;i++){const a=g.pts[i-1],b=g.pts[i],l=Math.abs(b.x-a.x)+Math.abs(b.y-a.y);if(l>best){best=l;m={x:(a.x+b.x)/2,y:(a.y+b.y)/2,hz:eq(a.y,b.y)};}}s+=m.hz?txt(P,m.x,m.y-8,e.label,'middle'):txt(P,m.x+8,m.y+4,e.label,'start');}
s+=multAt(P,g.p1,e.fromMult)+multAt(P,g.p2,e.toMult);
return s+'</g>';}
function shapeSVG(sh,P,isSel,ui){
const L=lay(sh),x=sh.x,y=sh.y,w=L.w,h=L.h,st=isSel?P.acc:P.ink,sw=isSel?2:1.25;
let s=`<g${ui?` data-s="${esc(sh.id)}"`:''}>`;
if(L.note){
s+=`<path d="M${x},${y}H${x+w-14}L${x+w},${y+14}V${y+h}H${x}Z" fill="${P.note}" stroke="${st}" stroke-width="${sw}"/><path d="M${x+w-14},${y}V${y+14}H${x+w}" fill="none" stroke="${st}" stroke-width="${sw}"/>`;
L.ls.forEach((l,i)=>{s+=`<text x="${x+PX}" y="${y+PAD+15+i*LH}" font-size="13" font-family="${F.text}" fill="${P.ink}">${esc(l)}</text>`;});
}else{
s+=`<rect x="${x}" y="${y}" width="${w}" height="${h}" fill="${P.card}"/><rect x="${x}" y="${y}" width="${w}" height="${L.hh}" fill="${P.head}"/>`;
let ty=y+PAD;
if(L.st){s+=`<text x="${x+w/2}" y="${ty+13}" text-anchor="middle" font-size="13" font-family="${F.text}" fill="${P.mut}">${esc(L.st)}</text>`;ty+=LH;}
s+=`<text x="${x+w/2}" y="${ty+15}" text-anchor="middle" font-size="15" font-weight="600" font-family="${F.disp}"${L.it?' font-style="italic"':''} fill="${P.ink}">${esc(sh.name)}</text>`;
s+=`<path d="M${x},${y+L.hh}H${x+w}M${x},${y+L.hh+L.ah}H${x+w}" stroke="${st}" stroke-width="1"/>`;
const rows=(arr,top,f)=>arr.map((m,i)=>{const by=top+PAD/2+13+i*LH;let r='';
if(m.v){if(ui)r+=`<rect data-vis="${esc(sh.id)}|${f}|${m.idx}" x="${x+PX-5}" y="${by-14}" width="18" height="${LH}" rx="3" fill="${P.head}"><title>${VISNAME[m.v]}: click to change</title></rect>`;
r+=`<text x="${x+PX+4}" y="${by}" text-anchor="middle" font-size="13" font-weight="600" font-family="${F.text}" fill="${P.ink}" pointer-events="none">${m.v==='-'?'−':esc(m.v)}</text>`;}
return r+`<text x="${x+PX+(m.v?16:0)}" y="${by}" font-size="13" font-family="${F.text}" fill="${P.ink}"${m.u?' text-decoration="underline"':''}${m.i?' font-style="italic"':''}>${esc(m.t)}</text>`;}).join('');
s+=rows(L.A,y+L.hh,'attrs')+rows(L.M,y+L.hh+L.ah,'methods');
s+=`<rect x="${x}" y="${y}" width="${w}" height="${h}" fill="none" stroke="${st}" stroke-width="${sw}"/>`;}
return s+'</g>';}
function drawDiagram(P,o){
let out='';const pre=o.ui?'m':'x';
const es=S.edges.slice();
const RT=routeAll(null);
for(const e of es){const g=RT.get(e.id);if(!g)continue;const isSel=false;
out+=edgeSVG(e,g,P,isSel?pre+'s':pre,isSel,o.ui);}
for(const sh of S.shapes)out+=shapeSVG(sh,P,false,o.ui);
return out;}
function bounds(){if(!S.shapes.length)return null;let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
const add=(x,y)=>{x0=Math.min(x0,x);y0=Math.min(y0,y);x1=Math.max(x1,x);y1=Math.max(y1,y);};
for(const s of S.shapes){const L=lay(s);add(s.x,s.y);add(s.x+L.w,s.y+L.h);}
for(const g of routeAll().values())g.pts.forEach(p=>{add(p.x-14,p.y-24);add(p.x+14,p.y+24);});CORR=null;
return{x:x0,y:y0,w:x1-x0,h:y1-y0};}
function exportSVG(P){const b=bounds();if(!b)return'';const pad=30,W=Math.ceil(b.w+pad*2),H=Math.ceil(b.h+pad*2),x=Math.floor(b.x-pad),y=Math.floor(b.y-pad);
return`<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="${x} ${y} ${W} ${H}"><defs>${mk('x',P.ink,P.paper)}</defs><rect x="${x}" y="${y}" width="${W}" height="${H}" fill="${P.paper}"/>${drawDiagram(P,{ui:false})}</svg>`;}

/* metrics (harness only) */
function metrics(){
const RT=routeAll(null);CORR=null;
const segs=[];let len=0,bends=0,hits=0;const rs=rects();
for(const e of S.edges){const g=RT.get(e.id);if(!g)continue;bends+=Math.max(0,g.pts.length-2);
for(let i=1;i<g.pts.length;i++){const a=g.pts[i-1],b=g.pts[i];len+=Math.abs(b.x-a.x)+Math.abs(b.y-a.y);segs.push({a,b,e});
for(const r of rs){if(r.id===e.from.id||r.id===e.to.id)continue;if(hit(a,b,r))hits++;}}}
let cr=0;
for(let i=0;i<segs.length;i++)for(let j=i+1;j<segs.length;j++){const u=segs[i],v=segs[j];if(u.e===v.e)continue;
const uh=eq(u.a.y,u.b.y),vh=eq(v.a.y,v.b.y);if(uh===vh)continue;
const H=uh?u:v,V=uh?v:u,y=H.a.y,x=V.a.x;
if(x>Math.min(H.a.x,H.b.x)+.5&&x<Math.max(H.a.x,H.b.x)-.5&&y>Math.min(V.a.y,V.b.y)+.5&&y<Math.max(V.a.y,V.b.y)-.5)cr++;}
const b=bounds();
return{crossings:cr,edgeBoxHits:hits,totalEdgeLength:Math.round(len),bends,width:Math.round(b.w),height:Math.round(b.h)};}
module.exports={S,setS,fromSpec,tidy,exportSVG,bounds,routeAll,lay,byId,metrics,DARK,GEN,GAPX,GAPY,MAXROW,snap,KINDS,mem};
