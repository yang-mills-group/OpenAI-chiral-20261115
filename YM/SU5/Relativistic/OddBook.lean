import YM.SU5.FiniteGaugeData.Tower.Atlas
import YM.SU5.Relativistic.OddStencil

/-! # The odd-resolution stencil belongs to this test system. Based on Tower.Atlas. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

open Reed (Fine think)
open Fock Pastry Tenant
variable (S:Finset Cover)(K':Calibration)(n:Side)
local notation "s₀"=> K'.c n
local notation "l₀"=> Satin.region S (K'.c n)
variable (t:Tivoli S (K'.c n))
local notation "φ"=> star (flake (Tset (K'.c n))ᶜ)
local notation "J"=> occupy S (K'.c n) (t.hosp)
noncomputable def fig (t:Tivoli S (K'.c n))(q:Singles S):ℂ:= (museum S (K'.c n) t.hosp q.val).choose
local notation "σ"=> fig S K' n t
lemma fig_unit (q:Singles S): ‖σ q‖=1:= (museum S (K'.c n) t.hosp q.val).choose_spec.1
lemma fig_ne (q:Singles S): σ q≠0:= norm_pos_iff.mp ((fig_unit S K' n t q).symm ▸ zero_lt_one)
lemma fig_expands (q:Singles S): twist φ ((velvet S (K'.c n)).tag q.val)= σ q • poke (q.val.map J):= (museum S (K'.c n) _ q.val).choose_spec.2

def scrip(A:FC (Single (K'.c n))) (q:Singles S):= (σ q)⁻¹ * crumb (twist φ A) (q.val.map J)
local notation "sliceA"=> scrip S K' n t
lemma biotech (A:FC (Single (K'.c n)))(q:Singles S):‖sliceA A q‖≤‖A‖:= by unfold scrip; rw [norm_mul,norm_inv,fig_unit,inv_one,one_mul]; exact (norm_entry ..).trans_eq (twist_norm ..)
lemma linearity{q:Singles S}(x y:FC (Single (K'.c n)))(z:ℂ):sliceA (z • x+y) q=z*sliceA x q+sliceA y q:=by unfold scrip; rw [map_add,twist_scalar,Pastry.crumb_add,Pastry.crumb_scale]; ring
lemma spliceC{q:Singles S}:Continuous (fun A=>scrip S K' n t A q):=by
 unfold scrip Pastry.crumb; apply Continuous.mul continuous_const; exact (breeze _).matrix_elem _ _
variable {f : Family K'}
lemma evaluated (a:Singles S→Purse S)(h:f=∑ q:Singles S,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n)): twist φ (f n x)=∑ q:Singles S,(a q).1 (Prod.map (onC _) (onC _) x) • (σ q • poke (q.val.map J)):=by
 rw [h]; simp_rw [Finset.sum_apply,map_sum,note_v,spool_sing,velvetTag,twist_scalar]; exact Finset.sum_congr rfl fun q _=> congrArg ((a q).val (Prod.map (onC _) (onC _) x) • ·) (fig_expands S K' n t q)
lemma recovered (a:Singles S→Purse S)(h:f=∑ q:Singles S,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n))(q:Singles S): sliceA (f n x) q=(a q).val (Prod.map (onC _) (onC _) x):=by
 unfold scrip
 rw [evaluated S K' n t a h x,crumb_sum,sum_eq_single q,crumb_scale,crumb_scale,Pastry.chip,if_pos rfl,mul_one,mul_left_comm,inv_mul_cancel₀ (fig_ne S K' n t q),mul_one]
 · intro j _ K0; rw [crumb_scale,crumb_scale,Pastry.chip,if_neg ?_,mul_zero,mul_zero]; exact fun x=> K0 (Subtype.ext (Finset.map_injective J x.symm))
 simp
lemma stitchedC {A:FC (Single (K'.c n))}(p: Fine (Tset s₀) (modesIn s₀ l₀) true A): A=∑ q:Singles S,sliceA A q • (velvet S (K'.c n)).tag q.val:=by
 obtain ⟨f,h,e⟩:= realizes_modes S K' n p; obtain ⟨a,v⟩:= circSingle S K' h
 let x:Fields (K'.c n):=(1,1)
 rw [←e x]; trans (∑ q:Singles S,note K' (a q).val (tagWord S q.val)) n x
 · rw [←v]
 simp_rw [Finset.sum_apply,note_v,spool_sing,velvetTag,recovered S K' n t a v x]

-- measurable Borel lifting of coefficients
variable (fP:Mark (K'.c n)) (h:AtSupport true (Satin.region S (K'.c n)) fP)
abbrev pieceC (q:Singles S)(x:PairsC):ℂ:= sliceA (fP (replant S (K'.c n) x)) q
include h
lemma painting (q:Singles S):Coeff true S (pieceC S K' n t fP q):=by
 refine ⟨fun _=>by contradiction,Girt.pole_w (fun v:PairsC=>fP (replant S (K'.c n) v)) (fun x=>scrip S K' n t x q) (spliceC S K' n t) (Env.along (g:=replant S (K'.c n)) h.env (replant_b S _)),?_⟩
 intro x y a b; exact congrArg (fun z=>scrip S K' n t z q) (h.dep _ _ (based S _ t _ _ a) (based S _ t _ _ b)) -- tune `..`
omit h
noncomputable def extendAtlas:Family K':=∑ q:Singles S,note K' (pieceC S K' n t fP q) (tagWord S q.val)
local notation "Ξ"=>extendAtlas S K' n t fP
include h
lemma OddList: InTest K' true S true Ξ:=by
 refine .sum _ _ fun (q:Singles S) _=>?_
 have ht:=Sound.note_t K' _ (painting S K' n t fP h q) (brand S q.val); rw [q.property] at ht; exact ht
lemma refunded: Ξ n=fP:=by
 funext x
 have hr: fP (replant S (K'.c n) (Prod.map (onC _) (onC _) x))= fP x:= h.dep _ _ (graft_native S _ t _) (graft_native S _ t _)
 unfold extendAtlas; simp_rw [Finset.sum_apply,note_v,pieceC,spool_sing,velvetTag,hr]; exact (stitchedC S K' n t (h.allV x)).symm

omit h
lemma levy {F:Family K'} (p: InTest K' true S true F){m:Side} (A:ℝ)(h:Hosp S (K'.c m))(v:∀ x, ‖F m x‖≤ A) : pay F ((Fintype.card (Singles S):ℝ)*A):=by
 obtain ⟨c,e⟩:= circSingle S K' p; have he:= rubySingle S K' F c e h A v
 intro a u; rw [e]; simp_rw [Finset.sum_apply]; exact ((norm_sum_le ..).trans (Finset.sum_le_sum fun t _=> (pitched K' (tagWord S t.val) (c t).val a u).trans (he ..))).trans_eq (by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])
lemma single_ext {m:Side}{F G:Family K'} (q:Hosp S (K'.c m))(x: InTest K' true S true F)(p:InTest K' true S true G)(w:F m=G m) : F=G:=by
 apply sub_eq_zero.mp; have h:= levy S K' (show InTest K' true S true (F-G) from by rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact x.add (.smul _ p)) 0 q (by rw [Pi.sub_apply, w, sub_self]; simp)
 funext n x; exact norm_eq_zero.mp (le_antisymm ((h n x).trans (by rw [mul_zero])) (norm_nonneg _))

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
