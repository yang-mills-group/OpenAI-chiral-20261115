
import Velour.Marocain.Comeback
import Velour.Gathers.Broderie
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}


local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

open Velour Work.C25

lemma press_joint {m:ℕ→Joint n →L[ℂ] H.Op}{r:Joint n →L[ℂ] H.Op}
 {q:Joint n→ℝ}(t:Continuous q)(u:q 0=0)
 (b:∀ f, ‖r f‖≤q f)(c:∀i f, ‖m i f‖≤q f)
 (h:∀f:𝓕,Gleams H (fun i=>m i (Joint.materialize n f)) (r (Joint.materialize n f)))(F:Joint n):
 Gleams H (fun i=>m i F) (r F):=by
 have e:Dense (span n:Set (Joint n)):=fun x=> 
    (show x∈(span n).topologicalClosure from 
         by rw [show (span n).topologicalClosure=⊤ from answer n]; exact Submodule.mem_top)


 have k:∀g∈span n, Gleams H (fun i=>m i g) (r g):=by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg=> obtain ⟨f,rfl⟩:=hg; exact h f
    | zero=> simp_rw [map_zero];exact Gleams.const _
    | add _ _ _ _ h k=>simpa only [map_add] using h.add k
    | smul _ _ _ h=>simp_rw [map_smul]; exact h.smul tendsto_const_nhds


 obtain ⟨P,a,e⟩:=mem_closure_iff_seq_limit.mp (e F)
 have d:Tendsto (fun i=>q (P i-F)) atTop (𝓝 0):=by
    rw [←u]
    refine (t.tendsto 0).comp ?_; simpa using e.sub_const F
 exact Gleams.uniform_joints
   (fun i=>k (P i) (a i))
   (fun i=> by rw [dist_eq_norm,←map_sub];exact b _)
   (fun i j=> by rw [dist_eq_norm,←map_sub];exact c _ _) d

lemma gleams_scroll {m:ℕ→𝓧}{r:𝓧} (t:∀j,Gleams H (fun i=>m i j) (r j)):
 Gleams H (fun i=>filepast (m i)) (filepast r):=by
 induction n with
 | zero=> simp [filepast]; exact Gleams.const _
 | succ n ih=>
    simp_rw [filepast_cons]
    exact (t _).mul (ih (fun j=>t _))




variable {m:ℕ→Fin n→H.Op}{r:Fin n→H.Op}

private lemma gleams_i {f:ℕ→H.Op}{g:H.Op}(h:Gleams H f g):
 ∃b:ℝ, ‖g‖≤b ∧ ∀i, ‖f i‖≤b:=by
 obtain ⟨c,q⟩:=h.bought
 obtain ⟨N,y⟩:=eventually_atTop.1 q
 obtain ⟨d,p⟩:= (finite_Iio N).image (fun i=>‖f i‖)|>.bddAbove
 refine ⟨max c d,(h.norm_paid q).trans (le_max_left ..),fun i=>?_⟩
 rcases le_or_gt N i with e|e
 · exact (y _ e).trans (le_max_left ..)
 exact (p ⟨_,e,rfl⟩).trans (le_max_right ..)

/-- Same eventual costs; strengthening to all i by increasing finitely.
Ribs etc offer independent cost estimates. -/
lemma gleams_flying (t:∀j,Gleams H (fun i=>m i j) (r j))(k:𝒦)
 {P:ℕ→Joint n}{Q:Joint n}(e:Tendsto P atTop (𝓝 Q)):
 Gleams H (fun i=>S.sail (m i) k (P i)) (S.sail r k Q):=by
 choose b p t' using (fun j=>gleams_i (t j))
 let q(x:Joint n):=lash a (festers n k) x * ∏j,b j
 have g(w:𝓧)(x:Joint n)(h:∀j,‖w j‖≤b j): ‖S.sail w k x‖ ≤ q x:=
   (S.feathers_bound ..).trans (mul_le_mul_of_nonneg_left
     (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>h _)) (lash_price ..))


 have l:Continuous q:= (lash_cont _).mul continuous_const
 have u:q 0=0:=by unfold q; rw [lash_zero,zero_mul]
 have h:Gleams H (fun i=> S.sail (m i) k Q) (S.sail r k Q) :=
    press_joint l u (fun f=>g _ f p) (fun i f=>g _ f fun j=> t' j i)
       (fun f=>by
         simp_rw [S.sail_pure]
         exact gleams_scroll fun j=> S.gleams_rise (t j) _ _) Q
 have l:Tendsto (fun i=>q (P i-Q)) atTop (𝓝 0):=by
      rw [←u]; refine (l.tendsto _).comp ?_; simpa using e.sub_const Q
 have x:Tendsto (fun i=> S.sail (m i) k (P i-Q)) atTop (𝓝 0):=
   squeeze_zero_norm (fun i=>g _ _ (fun j=> t' j i)) l
 simpa only [map_sub,sub_add_cancel,zero_add] using (Gleams.tightly x).add h
#print axioms gleams_flying



lemma coaches_surge (t:∀j,Gleams H (fun i=>m i j) (r j))(k:𝒦)
 {P:ℕ→Joint n}{Q:Joint n}(e:Tendsto P atTop (𝓝 Q)):
 S.Surges atTop (fun i=>S.coaches k (m i) (P i)) (S.coaches k r Q):=by
 intro v w h d
 have z(i:ℕ):= S.coach_refines k (m i) (P i) d (v i)
 simp_rw [z,S.coach_refines k r Q d w]
 exact (S.gleams_flying t _ e).both (h _)
#print axioms coaches_surge

