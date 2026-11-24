import YM.CF.Graph.Moth
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {α:Type*}{n:Side}{v r h u k b a x:ℝ}
-- Test arbitrary. observable cost poly. Field transport along ANY actual U even flags. 
structure Opt (n:Side)where
 o:Site n
 R:ℝ
 L:List α
 f:α→TagT
variable (S:Opt (α:=α) n) (P:Pane n)(q:Phys n)
def Opt.dial (S:Opt (α:=α) n):= S.L.length
def feel:ℂ:= valA S.o P S.R S.f S.L q
def feeP(k:ℝ):ℝ:= (k*180*n.val^6)^S.dial
lemma fee_p(h:0≤k):0≤feeP S k:=by unfold feeP; positivity
lemma bear (t:‖Emu.gain S.R‖≤ (n.val:ℝ)^2)(p: Yep k (mateK n) q a)(u:0≤a)(g:0≤k): ‖feel S P q‖ ≤ a*feeP S k:=by
 have he(v:SU.E): ‖wall S.o P v S.R S.f S.L q 0‖ ≤ a*feeP S k:=by
    let F(i:α):=nac S.o P v S.R (S.f i); let y:=k*180*(n.val:ℝ)^6
    have ht(i):Pays k (ton (F i)) y:=by
       let q:Ket (Single n):=(F i).2; have hp(j):‖q.ofLp j‖≤ (n.val:ℝ)^2:= (PiLp.norm_apply_le _ _).trans ((flo S.o P v _ _).trans_le t); refine (Pays.url q (F i).1 g).weigh ?_ g; unfold dialZ; exact (mul_le_mul_of_nonneg_right (sum_le_sum (fun i _=>hp i)) g).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,Pic.units_t]; unfold y; ring)
    unfold wall matchF; rw [mul_zero,sub_zero]; rw [zoneA,Emu.train,rollC,List.map_map]; rw [mul_comm a]; exact ((Pays.rollP (ton ∘ F) S.L ht).2 _ _ a u p).low -- feeP unfold
 have hx:= vigor S.o P S.R S.f S.L q 0 he; rw [mul_zero,sub_zero] at hx; exact hx
abbrev lite:ℝ:= ((n.val:ℝ)^2)^S.dial
lemma spentS(X:Type*)[LinearOrder X][Fintype X](A:FC X)(v:Wave X):‖acts A v‖ ≤ ‖A‖*‖v‖:= by apply ((acts A).le_opNorm v).trans; rw [show ‖acts A‖=‖A‖ from Matrix.l2_opNorm_toEuclideanCLM A]
lemma earn(t:‖Emu.gain S.R‖≤ (n.val:ℝ)^2) : ‖feel S P q‖ ≤ lite S *‖q‖:=by
 let N:ℝ:= n.val
 have he(v):‖zoneA S.o P v S.R S.f S.L‖ ≤ lite S:=by
    unfold zoneA Emu.train lite Opt.dial; generalize S.L=L; induction L with
    | nil=>simp [rollC]
    | cons i L ih=>
      let u:= Emu.nac S.o P v S.R (S.f i); change ‖ton u* rollC ton _‖ ≤ (N^2)^_; rw [List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul ((cost_pe ..).trans ((flo ..).trans_le t)) ih (norm_nonneg _) (sq_nonneg N))
 have hp:‖muni S.o P S.R S.f S.L‖ ≤lite S := (norm_integral_le_of_norm_le_const (Eventually.of_forall he)).trans_eq (by simp); let A:=muni S.o P S.R S.f S.L; exact (norm_inner_le_norm ..).trans (le_trans (le_of_eq (b:= ‖acts A q‖) (by rw [(tickB n).2,one_mul])) ((spentS _ A q).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _)))) -- tick namespace
section
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
private lemma kti(I:Type)[Fintype I][LinearOrder I](m:Wave I)(A:Orbit n→FC I)(Q:Orbit n→Wave I)(p:Envelope A)(h:Envelope Q):Envelope fun i=>inner ℂ m (acts (A i) (Q i)):=by
 let H(t:FC I)(x:Wave I):= inner ℂ m (acts t x); have hp:Continuous (uncurry H) := Continuous.inner continuous_const (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd)
 exact kitE A Q H hp p h
lemma earned (S:Opt (α:=α) n)(q:Orbit n→ Phys n)(B:Envelope q): Envelope fun i=> feel S i.1 (q i):=by
 let f(V: Pane n): FC (Single n):= muni S.o V S.R S.f S.L; have hf:Continuous f:= teg S.o S.R S.f S.L
 have he:Measurable (fun x:Orbit n=>x.1):=measurable_fst; -- scope
 have hk : Envelope (fun x:Orbit n=>f x.1):= refill f hf _ he
 exact kti (Single n) (mateK n) _ q hk B
end
end YM.CF.Graph
