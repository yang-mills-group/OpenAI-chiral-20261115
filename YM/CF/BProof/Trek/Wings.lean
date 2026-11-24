import YM.CF.BProof.Trek.Diff
/-! X slowly varying extension; taper pair path. Work with repaired gauge always. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side}{Y:Yard s}(D:Script Y){u v d:ℝ}{H:Herald u v}{t:ℕ}(C:Sized t H.whole)(g:Ratio c s)(B:Blocks Y c)(F:Bkg s)(f:Ratio a s)
namespace Script
local notation "CC"=> ChillF Y g B C.blockY
-- fill survivors X into r_mesh. dims zero initial field = supplied values (uses cost/dependencies only already price), including on unsafe sites: prefer set e0 there!
def guardX (x:Site s) := if x∈ CC then D.over x else apex
def XX (x:Site s) := expandX f (pin f CC) (D.guardX C g B) F x
def heat (x:Site s) := C.live CC x
def HH (x:Site s): ℝ→ Stamp:= if C.live CC x>0 then (fun i=> D.port C x (C.live CC x*i)) else fun _=>Pair.fullM (XX D C g B F f x).val
end Script
variable (L:Pad Y H C g.count.val)(T:4≤a.val)(W:f.count=H.whole)
-- lens requirements
structure Lamp (C:Sized t H.whole)(g:Ratio c s)(B:Blocks Y c)(d:ℝ)(U F: Bkg s):Prop where
 outside: Agrees (ChillF Y g B C.blockY) U F
 year : Guard F d
 calm : 0≤d ∧ d≤ H.calm
variable {U:Bkg s}{r:ℝ}(e:Lamp (Y:=Y) C g B r U F)
namespace Permit
variable (p:Permit D C U g B d) (S:Sound Y H C d)
local notation "Rₜ" => ChillF Y g B C.blockY
include e L T W p S
lemma awake {v':ℝ}(h:v'∈TimeR): PaceX (ChillF Y g B C.blockY) F D.over H.good ∧ SkinH (ChillF Y g B C.blockY) F (fun x=>D.port C x v') v := by
 obtain ⟨t,u⟩:= p.bothStep L S _ h; constructor <;> intro a i x y; · unfold EdgePrice; rw [←e.outside (a,i) x y]; exact t a i x y
 rw [←e.outside (a,i) x y]; exact u a i x y
lemma liftF : PaceX Set.univ F (D.XX C g B F f) H.yC:=by
 have ht:= (p.awake D C g B F f L T W e S timeR0).1 -- tune arg order
 let Z:= ChillF Y g B C.blockY; have hv:PaceX Z F (D.guardX C g B) (prie f.count):=by intro x i hx g₁; apply le_trans _ (W.symm ▸ H.genie); unfold Script.guardX EdgePrice; dsimp only; rw [if_pos hx,if_pos g₁]; exact ht x i hx g₁
 apply cover_cost f F _ (W ▸ H.whole_can) (D.guardX C g B) Z T hv; apply flat_m F (protectedX F e.calm.1 e.year) (Set.Subset.refl _) ((mul_le_mul_of_nonneg_left e.calm.2 xm_p.le).trans (W.symm ▸ H.ally))
omit T W in
lemma rise_fin (x:Site s)(h:¬ Y.Vic (tag Y x) C.nearM (time x) ∨ distant Y g B x 3): C.live (ChillF Y g B C.blockY) x=1:= C.live_far _ x (behold Y g B C L x h) -- tune incl bound
lemma base_here (x:Site s)(hx:Knob.aim (ChillF Y g B C.blockY) C.extentT x > 2*H.whole.val) : D.XX C g B F f x=D.over x := by
 let R':=C.extentT; let V:= ChillF Y g B C.blockY; let r:=2*H.whole.val; have hv (y:Site s)(q:separation x y≤ r):y∈V:= Knob.vital V _ x y (q.trans_lt hx)
 rw [Script.XX,enter_here _ _ _ _ _ (pin_safe f V _ T (fun y u=> hv y (show separation x y ≤ r from (by unfold r; rw [← W]; exact u)))),Script.guardX,if_pos (hv x (by simp))] -- tune
lemma awake_here(x y:Site s)(h: C.live (ChillF Y g B C.blockY) x >0)(u:separation x y≤1) : y ∈ChillF Y g B C.blockY ∧ D.XX C g B F f y = D.over y:=by
 let CC:=ChillF Y g B C.blockY; have ht:=Sized.live_in C _ x h; let r:=2*H.whole.val; have he: r < Knob.aim CC C.extentT y:=by
      have hx:=Knob.aim_var CC C.extentT x y; change r+1 < Knob.aim CC C.extentT x at ht; omega
 refine ⟨Knob.vital CC C.extentT y y ?_, base_here D C g B F f L T W e p S y he⟩; rw [separation_self]; omega
lemma HPort(x:Site s) : Money (D.HH C g B F f x) ∧ D.HH C g B F f x 0=Pair.fullM (D.XX C g B F f x).val:=by
 unfold Script.HH; split; swap; · exact ⟨quietM _ (sealX _ (vote_unit _)),rfl⟩
 rename_i h; obtain ⟨hx,hP⟩ := curvature D C U g B L p x; refine ⟨hx.shrink _ (C.live_z ..),?_⟩; simp only [mul_zero,hP]; rw [(p.awake_here D C g B F f L T W e S x x h (by simp)).2]
lemma speedH(v':ℝ)(h:v'∈TimeR): SkinH Set.univ F (fun x=>D.HH C g B F f x v') (2*v):=by
 let A:=D.port C; let X:= D.XX C g B F f; let K(x):= Pair.fullM (X x).val; let V:= ChillF Y g B C.blockY; let z:= C.live V; let J:= Knob.aim V C.extentT; have ht(x):z x∈ Zone:= C.live_z V x; let p':= p.liftF D C g B F f L T W e S;
 intro x i _ _; set y:=x+step i; have hi: separation x y ≤ 1:= immediate x i; let r:= F (x,i); have hu(q:Site s): ¬z q>0 →D.HH C g B F f q v'=K q:= fun h=> (by unfold Script.HH; rw [if_neg h])
 by_cases hp: z x>0∨ z y>0; swap;
 · dsimp only; rw [hu x (not_or.mp hp).1,hu y (not_or.mp hp).2]; unfold K; rw [compass]; apply (H.grant (scaledV r (X y)) (X x) (p' x i trivial trivial)).trans; nlinarith only [H.uf]
 have hx(t:Site s)(u: t∈ V ∧ X t=D.over t): D.HH C g B F f t v' = A t (z t*v'):=by
    unfold Script.HH; split; rfl; rename_i l; have he:z t=0:= by have hi:= (ht t).1; apply le_antisymm (le_of_not_gt l) hi
    change K t=_; rw [he,zero_mul,show A t 0=_ from (curvature D C U g B L p t).2]; unfold K; rw [u.2]
 have he:x∈V ∧ X x=D.over x:= hp.elim (fun h=> awake_here D C g B F f L T W e p S x x h (by simp)) (fun h=>awake_here D C g B F f L T W e p S y x h ((separation_comm ..).trans_le hi))
 have hy:y∈ V ∧ X y=D.over y:= hp.elim (fun h=> awake_here D C g B F f L T W e p S x y h hi) (fun h=>awake_here D C g B F f L T W e p S y y h (by simp)); dsimp only; rw [hx x he,hx y hy]; have hℓ(x:Site s): z x*v'∈ TimeR:= ⟨mul_nonneg (ht x).1 h.1,(mul_le_of_le_one_left h.1 (ht x).2).trans h.2⟩
 apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (motion r (A y (z x*v'))) _); rw [two_mul]; refine add_le_add ?_ ((p.awake D C g B F f L T W e S (hℓ x)).2 x i he.1 hy.1) -- tune underscores
 · change _≤_; rw [show F (x,i)=r from rfl,motion_frame]; apply le_trans ((curvature D C U g B L p y).1.budget _ _ (hℓ y) (hℓ x)); rw [←sub_mul,abs_mul,abs_of_nonneg h.1]; exact ((mul_le_mul_of_nonneg_left (mul_le_mul (C.payW V y x ((separation_comm ..).trans_le hi)) h.2 h.1 (div_nonneg rate_p.le (by positivity))) rate_p.le).trans ((show rateH*(rateH/↑C.taperW*2)=rateH*2*(rateH/↑C.taperW) from (by ring)).trans_le S.tap)) -- parentheses?
end Permit
end YM.CF.BProof.Trek
