import YM.SU5.FiniteGaugeData.Hierarchy.Salon
/-! # The transition receipt on an actual election entry, including the chosen fee field and beta. This represents the advanced mark as a wide Family, with a common norm bound for each step at a fixed s and S. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)

local notation "T₀" => plaza (Λ:=Λ) S
local notation "W₀" => GridStep Λ l S
local notation "Q" => ingress Y s i k

structure Solvent : Prop where
  lower : Tipping (plaza (Λ:=Λ) S) (side Y i s) (VolumeCape.Dream.plot l).C
  upper : Roomy (GridStep Λ l S) (side Y i (s+1))

structure Offered : Prop where
  calendar : (Y.voyage i).kick ≤ k
  age : s< Y.uv k
  bill : Solvent Y S s i

abbrev PaidPt := {a:ℕ×ℕ // Offered Y S s a.1 a.2}

variable {i k}
include h in
lemma solvent_often : ∀ᶠ i:ℕ in atTop, Solvent Y S s i:=by
  have w(T:Finset Cover)(s):∀ᶠ i:ℕ in atTop,Hosp T (side Y i s):= by
    filter_upwards [(momentum Y s).eventually (separates Kₜ T)] with i U
    rw [show side Y i s=(tent Y h).c (momentm Y i s) from (terrain Y h (Y.ir i) s).symm]; exact ⟨U⟩
  filter_upwards [w (tips (porch C₀ T₀)) s,w (tips W₀) (s+1)] with i V U; exact ⟨V.seat_,U⟩
lemma solvent_lower (p:Solvent Y S s i):Hosp S (side Y i s):= hosp_mono (S:=S) (T:=tips (porch C₀ T₀)) ⟨p.lower⟩ (fun _ v=>tips_here _ (porch_here C₀ T₀ (liner_here S (Advance.nearZero _) v)))

variable (p: Offered Y S s i k)
def transit (f:Catalog S) : Catalog (GridStep Λ l S) :=
  Classical.choose (sold_surj Y h (GridStep Λ l S) (s+1) i p.bill.upper
    (ingress Y s i k (sold Y h s i (composeQ Kₜ S f)))
    (ingress_grid Y S s i k p.calendar p.age (sold_affair Y h S s i (compose_t S Kₜ f))))
lemma exchanged (f:Catalog S) : sold Y h (s+1) i (composeQ Kₜ W₀ (transit Y h S s p f))=Q (sold Y h s i (composeQ Kₜ S f)):= Classical.choose_spec (sold_surj Y h W₀ _ _ p.bill.upper _ (ingress_grid Y S _ _ _ p.calendar p.age (sold_affair Y h S s i (compose_t S Kₜ f))))

def transitionL : Catalog S →ₗ[ℂ] Catalog (GridStep Λ l S) where
  toFun f:= transit Y h S s p f
  map_add' x y := by
    apply sold_catalog_inj Y h W₀ _ _ (roomy_hosp _ p.bill.upper)
    dsimp only
    rw [map_add,map_add,exchanged,exchanged,exchanged, map_add,map_add, ingress_add Y s i k p.calendar p.age (sold_affair Y h S s i (compose_t S Kₜ _)) (sold_affair Y h S s i (compose_t S Kₜ _))]
  map_smul' c y:=by
    apply sold_catalog_inj Y h W₀ _ _ (roomy_hosp _ p.bill.upper)
    dsimp only
    rw [RingHom.id_apply,map_smul,map_smul,exchanged,exchanged,map_smul,map_smul,ingress_scale]

lemma transition_apply (f:Catalog S) : transitionL Y h S s p f=transit Y h S s p f:=rfl
lemma transition_reads (f:Catalog S) : sharp Y h s i k (composeQ Kₜ S f) = sharp Y h (s+1) i k (composeQ Kₜ W₀ (transitionL Y h S s p f)):=by rw [refresh Y h S s i k p.calendar p.age _ (compose_t S Kₜ f),sold_sharp (s:=s+1),transition_apply,exchanged]
lemma transition_finance (f:Catalog S) :
    source W₀ (transitionL Y h S s p f)= takeScore W₀ (roomy_hosp _ p.bill.upper) (Q (sold Y h s i (composeQ Kₜ S f))) := by rw [← sold_q (S:=W₀) (Y:=Y) (h:=h) (p:=roomy_hosp _ p.bill.upper),transition_apply,exchanged]
include p
lemma ingress_compose_sum (f:Catalog S):
    Q (sold Y h s i (composeQ Kₜ S f)) =∑ x:Key S, Q (Satin.knot (side Y i s) (Typeset S x) (source S f x)):=by
  change Q ((sold Y h s i) (∑ x:Key S, note Kₜ (source S f x) (Typeset S x)))=_
  generalize he : (univ: Finset (Key S))=T
  classical
  let A(x:Key S):= note Kₜ (source S f x) (Typeset S x)
  have hx(x: Key S): InTest Kₜ true S false (A x) := x.property ▸ note_t Kₜ (tagWord S x.val) (f x).property (brand S x.val)
  change Q ((sold Y _ s i) (∑ x∈T,A x)) = _
  clear he
  induction T using Finset.induction_on with
  | empty=>
    rw [sum_empty,sum_empty,map_zero]; exact (by simpa only [zero_smul,smul_zero] using ingress_scale Y s i k 0 0)
  | insert x T t ih=>
    rw [sum_insert t,sum_insert t,map_add, ingress_add Y s i k p.calendar p.age (sold_affair Y _ S s i (hx x)) (sold_affair Y _ S s i (InTest.sum T _ (fun a _=>hx a))), ih]; unfold A; rw [sold_kiosk]
#print axioms exchanged
end YM.CF.Buffered.Afterglow.Hierarchy
