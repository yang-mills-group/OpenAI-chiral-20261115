import YM.CF.Gloss.Feast
import YM.CF.Gloss.Book
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable{m B L:Side}{j:ℕ}{o:Odd L.val}
open Paige Vault Dial Brace
variable {T:Pricing j L o (Thread j)}{e:ℝ}{P:Grasp T B e}(X:Pearl P)(D:Stamped j L o T)(h:1 ≤ j)(g:P.roundZ ≤(CSide m B).val)(q:0 < e)
local notation "p"=>northZ m B
variable {W:Scroll m B (Brace.northZ m B)} {a c:ℝ}(H:ScaleK a c W)
include X D h g q H
lemma cry_q (V: Pack m B)(l:V∈payer m B e): (Phase.fund m B p V.1 V.2)-cabinQ W V=∑ i:costG m B,seedQ W i V:=by
 rw [sub_eq_iff_eq_add]; unfold cabinQ; rw [←sum_add_distrib,Fintype.sum_prod_type]; let Z:=Phase.fund m B (northZ m B) V.1 V.2; let K:=rip m
 have hp(s:Era m): ∑ i: Stamp m B,(seedQ W (s,i) V+billP W (s,i) V)=K • Z:=by
    simp_rw [seedQ,billP,workQ,←smul_add,← pay_a,Scroll.leftover,sub_add_cancel]; rw [←smul_sum,← pay_m]; congr 1; let Y:=vest B s V; change payZ s (∑ i,W.value i none Y)=Z; have hh:= war_v B s X D h g q V.1 l.1 V.2 l.2; rw [taxed H P.baseY (voxel B s e V l), show Phase.fund m B (northZ m B) Y.1 Y.2=payZ s Z from hh,pay_u]
 simp_rw [hp,sum_const,card_univ]; rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,show (_:ℝ)*K=1 from mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]
end YM.CF.Gloss
namespace YM.CF.RP.Str
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
open Gloss
variable (U : ScaleK A D W) (g : Budget B e d)
include U g
lemma cabis(p:Geometry (CSide m B))(x: Pack m B)(h:x∈payer m B e): cabinQ W (nextG p x)=cabinQ W x:=by
 apply sum_congr rfl; intro i _; obtain ⟨k,hk⟩:=squirm B i.1 p x; unfold billP workQ nextG; rw [hk,(gainS U g i.2).gaugeEq _ _ (voxel B i.1 e x h)] -- tune
lemma ceremonyF (t a : ℝ) (p : Foot m B) (v : Geometry (CSide m B)) (f : Test m B) : rawEF W e β t a p (rideG m B v f)=rawEF W e β t a p f := by
  unfold rawEF; nth_rw 2 [← (inspect (m:=m) (B:=B) v).integral_comp (appoint v)]; apply integral_congr_ae; apply Eventually.of_forall; intro x; unfold ratioRF
  by_cases k:x∈ TallyR m B e β
  · have hp := tallyP k; let S := nextG v x
    let Y := v ∘ node (N:=CSide m B); let V := conjG matter Y; let A := quantU (n:=Xmind m B) V
    have hA : acts A.val (linearB _)=linearB _ := ref_frame Y
    have he : pairWave (n:=Xmind m B) (pair m B S.1 S.2)=acts A.val (pairWave (pair m B x.1 x.2)) := by
      have ht := pair_g x.1 x.2 v; rw [show pair m B S.1 S.2= congrC V _ from ht,congrC, ← pair_cov]; rfl
    let H := wiel m B p S.1
    have hH : H=twist V (wiel m B p x.1) := by unfold H wiel; rw [show links S.1=Lattice.gauge Y (links x.1) from links_g ..]; exact twistH ..
    let F := rideG m B v f
    have hF : f S= twist A (F x) := by
      have he := twist_inv (star A) (f S); rw [star_star] at he; exact he.symm
    change (TallyR m B e β).indicator _ _ = (TallyR m B e β).indicator (amplitudeF W p β t a f) (nextG v x)
    rw [Set.indicator_of_mem k, Set.indicator_of_mem ((anew ..).mpr k)]; unfold amplitudeF; rw [net_price, show cabinQ W (nextG v x)=_ from cabis U g v _ hp]
    apply congrArg; change _=inner ℂ _ (acts (f S*quant (n:=Xmind m B) (grow H _)) (pairWave (pair m B S.1 S.2)))
    rw [hF,hH,he,←quant_flow]; change _=inner ℂ _ (acts (twist A _*twist A _) (acts A.val _)); rw [←map_mul]; exact (bra V hA _ _).symm
  simp only [Set.indicator_of_notMem k]; rw [Set.indicator_of_notMem (fun z=>k ((anew v x).mp z))]
end YM.CF.RP.Str
