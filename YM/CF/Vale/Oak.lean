import YM.CF.Hom.Sally
import YM.CF.Newt.Stage
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
local notation "G5"=> SU.group
variable {K:Teller G5}{P:Patch}{R:ChartRatio G5}{W:Postal}{η:ℝ}{n:ℕ}
-- Calendar pure library from UV. common for all depths.
structure Gold (K:Teller G5) (P: Patch)(R:ChartRatio G5)(W:Postal) where
 lobby :P.J=K.j
 below :K.below=K.top
 robe: Claims K R P W
 cloth: P.Branches K.bind G5
 H:ℕ→Bed
 f:ℕ→Flight K.j K.j
 lent(i): (f i).patch=P
 Z:(i:ℕ)→Towers (f i).L
 deed (i):Paddle (f i) K.bind (H i) (H (i+1)) K.top.clip (Z i) K.η K.C
 roof (i):MainIn G5 K.top.clip (H i) W.parcel K.η K.C
 path:ℕ → PathData G5
 tied(i):Attached (H i) (path i)
 mood(i): (path i).Bounds K.top.clip K.top.width K.top.paths W.bar
 born:path 0= solvent (WilsonStartup.Design.top G5 K.top.clip)
 ring (i):Rare (path i)
 charge:ℕ→ℝ
 bound (i): |charge i + SU.group.slopeConstant*Real.log P.L.val|+1≤K.top.drift
 sold(i): Signets (f i) K.bind (Z i) K.top.clip (path i) (path (i+1)) (charge i) R W.peak W.rise W.gap W.n
lemma coin (v:Linear K n η)(x: n≤P.L.val)(e:P.J=K.j)(g:Claims K R P W)(p:W.parcel=η) : Nonempty (Gold K P R W):=by
 subst η
 obtain ⟨H,h,A,Y⟩:=v.issue P x e
 choose f hf Z hZ using Y
 let J(i:ℕ):= {y:PathData G5// Attached (H i) y∧y.Bounds K.top.clip K.top.width K.top.paths W.bar∧Rare y}
 let r:J 0:= ⟨_,h,v.old W.bar W.rental⟩
 have he(i:ℕ)(X:J i) : ∃ q':J (i+1),∃ a:ℝ,|a+SU.group.slopeConstant*Real.log P.L.val|+1≤K.top.drift ∧ Signets (f i) K.bind (Z i) K.top.clip X.val q'.val a R W.peak W.rise W.gap W.n:=by
    obtain ⟨V,hV,hT,hP,a,ha,hd⟩:= g.note (f i) (H i) (H (i+1)) (Z i) X.val (hf i) W.parcel (hZ i) (A i) (A (i+1)) X.2.2.1 X.2.2.2 X.2.1 rfl
    exact ⟨⟨V,hP,hV,hT⟩,a,hf i ▸ (show |a+SU.group.slopeConstant*Real.log (f i).patch.L.val|+1≤ K.top.drift from ha),hd⟩
 choose V t hv hs using he
 let X:(i:ℕ)→ J i:= Nat.rec r V
 exact ⟨⟨e,v.stable.symm,g,v.oath P,H,f,hf,Z,hZ,A,fun i=> (X i).val,fun i=>(X i).2.1,fun i=>(X i).2.2.1,rfl,fun i=>(X i).2.2.2,fun i=> t i (X i),fun i=>hv i (X i),fun i=>hs i (X i)⟩⟩
namespace Gold
variable {c f:Side}(A:Gold K P R W)
lemma lent_L(i:ℕ):(A.f i).L=P.L:=congrArg Patch.L (A.lent i)
variable (i:ℕ)(x:f.val=c.val*P.L.val)
include x
lemma sized : f.val=c.val*(A.f i).L.val:=by rw [A.lent_L i]; exact x
abbrev op:= (A.f i).visit K.bind (A.sized i x)
lemma patch_x : (A.op i x).patch=P:= A.lent i
abbrev mint := Tube.mk (S:=A.op i x) (A.Z i) (A.path i) K.top.clip (A.path (i+1)) K.top.clip
lemma booth : Lift.Booth K (A.op i x) (A.mint i x):=by
 have ht:= A.deed i; have hr:=ht.roll (A.sized i x)
 have hu: K.Funds (A.op i x) (A.mint i x):=by
    refine ⟨rfl,rfl,(by rw [A.patch_x]; exact A.cloth), ht.pay, ?_,rfl,?_,⟨_,_,A.tied i,A.tied (i+1),hr⟩⟩ -- motive error cloth
    · exact congrArg Stage.clip A.below.symm
    exact ⟨_,_,A.mood i,A.below.symm ▸ A.mood (i+1)⟩
 let H:= A.roof i; let J:= A.roof (i+1)
 exact ⟨hu,A.H i,A.H (i+1),_,_,_,_,H.2.1 _,J.2.1 _,A.tied i,A.tied (i+1),H.2.2 _,J.2.2 _,ht.link (A.sized i x),hr⟩
lemma cert (p:W.n≤c.val)(s:ℝ)(h:100*(1+radiusB s)≤c.val):Newt.Cert P K (A.op i x) (A.mint i x) s:=by
 have he:A.op i x= ⟨P,K.bind,x⟩:=by
    cases h: A.op i x with
    | mk Y Z t =>
      have ht:Y=P:= Eq.trans (congrArg StepData.patch h.symm) (A.lent i)
      have hv:Z=K.bind:= Eq.trans (congrArg StepData.kernel h.symm) rfl; congr
 exact ⟨A.lent i, A.booth i x,h, he.symm ▸ (A.robe.bound x p)⟩ -- motive
end Gold
end YM.CF.Vale
