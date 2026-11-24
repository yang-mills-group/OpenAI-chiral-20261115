import YM.CF.BProof.Hero.Belt
/-! B-N Mark before gauge change. Use raw axial frame with the shared seam & face h.
On a slightly extended collar `room`, U in those frames has small links.
This is not a claim under arbitrary reading before the actual D/N tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mark
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}(a:Per s)(l:ℕ)(S: Hall s)(U:Bkg s)(b:Eyes s)(g:Ratio c s)(y r m:ℝ)
def AngleZone(l u:ℕ):Prop:= u*4≤l ∨ l*3≤u*4
lemma taper_edge (x:Site s)(hx:x∈room a g l)(W:Width g l): let u:=along a (time x); AngleZone l u :=by
 have hl:=hx.2; change _ ≤ _ at hl; have he:=mem_strip.mp (show x∈ BProof.strip a l from hx.1); unfold Width at W; unfold chip life at hl; unfold AngleZone; dsimp only; omega
lemma angle_edge (W:Width g l)(x:Site s)(hx:x∈room a g l): angle l (along a (time x))=if flag a (time x) l then 1 else 0:=by
 obtain hh:= taper_edge a l g x hx W; let u:=along a (time x); have hl:0<l:=by unfold Width at W; omega
 unfold AngleZone at hh; split <;> rename_i h; apply angle_one l hl; have hv:= (flag_true ..).1 h; unfold cut at hv; omega; apply angle_zero l hl; have hv:= (flag_false a (time x) l).1 (Bool.eq_false_iff.mpr h); unfold cut at hv; omega
-- generic N Collar pack
structure Facing : Prop where
 lifts : Angular.lifts a l y S U b
 frames : ∀ i, BProof.Face.Firm S.K (Angular.outlook a l S U b i) r m
 toll : ∀ i∈ washes a l, cd SU.group (formal a l S U b i) (hall a l S U b i)≤xi y
 roof : Calm a l U (tip g.count)
-- construct from actual costs call later
lemma facade (v:l+1<s.val)(hl:0<l)(h:Angular.lifts a l y S U b)(e:∀ i,BProof.Face.Firm S.K (Angular.outlook a l S U b i) r m)(p:∀ i∈ watches a l, cd SU.group (formal a l S U b i) (hall a l S U b i)≤xi y)(t:Calm a l U (tip g.count)): Facing a l S U b g y r m:=by
 refine ⟨h,e,fun i w=>?_,t⟩; by_cases v':i∈watches a l; exact p i v'; rw [same_frame a l S U b v hl e i w v', cd_self]; exact (coin_pos ..).le
-- book
variable {y r m}(W:Width g l)(h:2*l<s.val)(f:Facing a l S U b g y r m)
abbrev gown := stage a l U b
include f W
lemma price_horiz (x: Per s)(p:Space s)(j:TAxis)(hp:join x p∈ room a g l) : SU.group.chord (Lattice.gauge (gown a l U b) U (horiz x p j)) ≤ allowance y + xi y:=by -- allowance? notes check
 let d:= flag a x l; let i:= (p,j); let q:=p+tstep j; let X:= inlet a l U d i; let F:= Angular.sight a l S U b d; let J(t:Space s):= b d t*(F t)⁻¹; let T:=Angular.outlook a l S U b d i; let B:=hall a l S U b (horiz x p j); let A:=J p*T*(J q)⁻¹
 have he(t): gown a l U b (join x t)= J t* V a l S U b (join x t):= by unfold gown V; rw [stage_move, stage_move (g:= Angular.sight a l S U b)]; change _= J t*(F t*_); dsimp only [J,F,d]; group
 have hv:A= b d p * X * (b d q)⁻¹:= by dsimp only [A,J,T,Angular.outlook, X,F, BProof.Face.react,q,i]; group
 have ht: formal a l S U b (horiz x p j)=T:=by
   have he:= angle_edge a l g W (join x p) hp; rw [time_join] at he; skip -- not tactic T dependency issue
   rw [horizontal_light]; unfold Angular.light BProof.Face.profile; rw [he]; cases e:flag a x l; rw [show T=Angular.outlook a l S U b false i from ?_]; exact BProof.Face.link_a S.K _ _ ((f.frames false).pay _); dsimp only [T,d]; rw [e]; rw [show T=Angular.outlook a l S U b true i from ?_]; exact BProof.Face.link_b S.K _ _ ((f.frames true).pay _); dsimp only [T,d]; rw [e] -- tune
 have hu: Lattice.gauge (gown a l U b) U (horiz x p j)=J p*B*(J q)⁻¹:=by dsimp only [B,hall,horiz,Lattice.gauge,q]; rw [←step_join,he,he]; group
 rw [←cd_one,hu]; apply (cd_triangle _ _ A _).trans; apply add_le_add
 · rw [cd_one,hv]; exact (BProof.Face.follow_chord ..).mp ((f.lifts d).2 p j)
 change cd SU.group (J p*T*(J q)⁻¹) _ ≤ _; rw [cd_mul_right,cd_mul_left,←ht]; apply f.toll; apply (mem_wash ..).2; apply (wet_h ..).2; exact mem_strip.mp (show join x p∈ BProof.strip a l from hp.1)
include h
lemma price_belt (x:Site s)(i:Axis)(hx:x∈room a g l)(hp:x+step i∈room a g l): SU.group.chord (Lattice.gauge (gown a l U b) U (x,i))≤ allowance y+xi y:=by
 let k:Bond s:=(x,i); have he(t:Bond s)(e:t=k): t.1∈ room a g l ∧ t.1+step t.2∈room a g l:= e ▸ ⟨hx,hp⟩; change SU.group.chord ((Lattice.gauge (gown a l U b) U) k) ≤ _; rcases Angular.whichBond k with ⟨y,p,t⟩|⟨y,p,j,t⟩
 · rw [t]; have hl:= he _ t.symm; have hz:= taper_edge a l g _ hl.1 W; let r:= along a y; have hk:r ≤ l:=mem_strip.mp (show (vert y p).1∈ BProof.strip a l from hl.1.1); rw [stage_normal a y l U b _ _ p, Gauge.chord_one]; exact add_nonneg (coin_pos ..).le (coin_pos ..).le; unfold Width at W; change r+1<s.val -- tune `<` proof s.val
   omega
   change AngleZone l r at hz; change r≠cut l; unfold AngleZone at hz; unfold Width at W; unfold cut; omega
 rw [t]; exact price_horiz a l S U b g W f y p j (he _ t.symm).1
end YM.CF.BProof.Mark
