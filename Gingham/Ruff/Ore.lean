import Gingham.Ruff.Currency
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Shells Fan
variable {n:ℕ}{a c e ρ b:ℝ} (X:Rialto n e ρ b)
   {R: Seal (Seat N)→Prop} {A:Fob N e}
   {y:Site N}{u:Side}
variable (B:Buttons N e R a c A)(D:∀ S,R S → Girder y u S)
variable {t:ℝ}

def sprays (o:Seat N)(v:Doub N)(t:ℝ):Prop:= 0≤t ∧ ∀ (i: Edge (Seat N)),
 ‖(v.1 i,v.2 i)‖ ≤ t*(1+(separation o i.1:ℝ))

def shaved (S: Seal (Seat N))(x:Doub N): Doub N:=
 (fun i=>if i.1∈S then x.1 i else 0,fun i=>if i.1∈S then x.2 i else 0)

lemma shaved_length (v:Doub N)(h:sprays (bouton y) v t)
   (S:Seal (Seat N))(p:Girder y u S):
 ‖shaved S v‖ ≤ t*walk u S.card:=by
 have w:0≤t*walk u S.card:=mul_nonneg h.1 (walk_nn ..)
 have k:∀ i:Edge (Seat N),max ‖(shaved S v).1 i‖ ‖(shaved S v).2 i‖ ≤ t*walk u S.card:=by
  intro i
  unfold shaved; dsimp
  by_cases q:i.1∈S
  · rw [if_pos q,if_pos q]
    have d:(separation (bouton y) i.1:ℝ) ≤ ((widthL u+5*S.card:ℕ):ℝ):=
       Nat.cast_le.mpr (p _ q)


    have c' := h.2 i; rw [Prod.norm_def] at c'
    exact c'.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl d) h.1)
  simpa [q] using w
 rw [Prod.norm_def]
 exact max_le ((pi_norm_le_iff_of_nonneg w).mpr fun i=>(le_max_left ..).trans (k i))
   ((pi_norm_le_iff_of_nonneg w).mpr fun i=>(le_max_right ..).trans (k i))


include X
lemma palest (j:3≤n) (S:Seal (Seat N)) {v w:Doub N}
   (g:∀i:Edge (Seat N),i.1∈S→i.1+step i.2∈S→v.1 i=w.1 i∧v.2 i=w.2 i):
 quadraticChi (hum X (B.mark S)) v = quadraticChi (hum X (B.mark S)) w:=by
  let G:=B.mark S
  have H := (Gallery.sub (aria X (B.pass S)) 3 j)
  have K:= flat_aria X (B.pass S) (by omega)
  have L(q:Doub N):∀ᶠ s:ℝ in 𝓝[>] 0, ‖s • q‖<1:=
     (((continuous_id.smul continuous_const).norm.tendsto 0).eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds -- 
  have e:∀ᶠ s:ℝ in 𝓝[>] 0,hum X G (s • v)=hum X G (s • w):=by
    filter_upwards [L v,L w] with r a c
    suffices G (pate X (r • v))=G (pate X (r • w)) from congrArg (fun x=>Matrix.trace x) this


    have hx:Agrees S (dabble ρ (r • v)) (dabble ρ (r • w)):= by
      intro i p t
      obtain ⟨o,m⟩:=g i p t
      simp only [dabble,pencil,a,c,if_true,Prod.smul_fst,Prod.smul_snd,
        Pi.smul_apply,o,m]
    ext i k
    refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_trans (((B.pass S).expo i k).variation _ _) ?_))
    dsimp only [pate] --?
    change _ * (fare S (Tulip.profile _) (Tulip.profile _)/ _ )≤_
    rw [fare_cyl hx,zero_div,mul_zero]
  exact tendsto_nhds_unique
    ((quadraticChi_pressure H K v).congr' (e.mono fun r d=>
      congrArg (fun z:ℂ=> (r^2)⁻¹ • (z-hum X G 0)) d))
    (quadraticChi_pressure H K w)

include B D
lemma incision (l:0<a)(j:3≤n){v:Doub N}(g:sprays (bouton y) v t):
 ‖quadraticChi (hum X A) v‖ ≤ Interest u a c 2*t^2:=by
  rw [columnChi X B l.le j]
  refine ((norm_sum_le ..).trans (sum_le_sum fun S _=>?_)).trans (tribute B u l g.1 2)
  let G : Gallery 2 (hum X (B.mark S)) (blush (B.cost S)):= Gallery.sub (aria X (B.pass S)) 2 (by omega)
  by_cases h: blush (B.cost S)=0
  · simpa [blood,h] using quadraticChi_small G v


  have z:=D S (apple_positive B S h)
  rw [palest X B j S (w:=shaved S v) (by intro i a _;simp [shaved,a])]
  refine le_trans (quadraticChi_small G _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (shaved_length _ g _ z) 2) (apple_fee ..))

#print axioms incision

