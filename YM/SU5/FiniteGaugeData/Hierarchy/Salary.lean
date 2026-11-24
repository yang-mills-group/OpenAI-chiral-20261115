import YM.SU5.FiniteGaugeData.Hierarchy.Pas
/-! # Uniform bound & Menu for image on the election -/
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
local notation "W₀" => GridStep Λ l S

section
variable {I:Type*}(P:I→ PaidPt Y S s)(A:I→ Catalog S) (C:ℝ)(p:∀i,‖A i‖≤C)
local notation "n" i:max => side Y (P i).val.1 (s+1)
local notation "m" i:max => side Y (P i).val.1 s
local notation "Q" i:max => ingress Y s (P i).val.1 (P i).val.2
include h p C
set_option maxHeartbeats 400000 in
private lemma reading_knot (a:Key S): Menu (T:=fun i:I=> FC (Single (side Y (P i).1.1 (s+1)))) (fun (i:I) (x:PairsC)=> ((Q i) (Satin.knot (m i) (Typeset S a) (source S (A i) a))) (replant W₀ (n i) x)):=by
  rcases isEmpty_or_nonempty I with v|v
  · exact Menu.congr (Menu.zero (T:=fun i:I=>FC (Single (n i))) (X:=PairsC)) (fun i=>isEmptyElim (i:I))
  let N(i):Side:= side Y (P i).1.1 s; let L(i):Side:=side Y (P i).1.1 (s+1)
  let t(i:I):= (P i).1.1; let k(i:I):= (P i).1.2
  let u:I:=Classical.choice v
  have hb(i:I): (Y.voyage (t i)).kick≤ k i:= (P i).property.calendar
  have hT(i:I): s< Y.uv (k i):=(P i).property.age
  let G(i):= apt (Y.ir (t i)) Λ.block L₁ s
  let F(i):=replant W₀ (L i)
  have hz:= (crease Y s _ _ (hb u) (hT u)); have he : Λ.R.Branches Λ.K.bind SU.group:=Λ.V.L.cloth
  let J:=Σ i:I, Edge (Seat (L i))
  have hF: Chalk.Fin (fun (v:J) (x:PairsC)=>(F v.1 x).2 v.2):= Chalk.graft_link W₀ _ (f:=Prod.snd) (fun v:J=> v.2)
  have hv:Deal (fun (v:J) (x:PairsC)=>(F v.1 x).2 v.2):= Chalk.deals hF (fun i=> ((measurable_pi_apply _) |>.comp (measurable_snd.comp (replant_b ..))))
  simp_rw [reel];
  refine FineSide (I:=I) (plaza (Λ:=Λ) S) Λ.R Λ.K.bind he (N:=N) (P:=L) (fun i=> sized Y s (t i)) Λ.K.j D₀ (Journey.legal Λ) Λ.R.odd_side Chi.canonical Λ.J.d hz.1 hz.2 (fun i=> rayCost Y s (t i) (k i)) _ _
     (fun i=> (Xᵣ (t i) (k i)).pull.tip s (hT i)) (fun i=> abs_le.mpr (Y.seated s (t i) (k i) (hT i))) C₀ (Dream.plot l).K F (Chalk.graft_link W₀ _ (f:=Prod.fst) (fun v:J=>v.2)) hv (fun i=>measurable_fst.comp (replant_b ..)) (fun i=> source S (A i) a) C (fun i x=>(price_letter S (A i) a x).trans (p i)) _ S (fun i=> ?_) (fun i=> Wₐ (t i) s) (liner_here S _) (fun i=> Satin.linen_contains ..) (fun i=> (P i).property.bill.lower) (fun i=> (Y.voyage _).craft s) (fun i=> ((Y.voyage _).ownership s).paid.bill)
  rw [← sold_kiosk Y h (i:=t i)]; exact sold_affair Y h S _ _ (note_t Kₜ (tagWord S a.val) ((A i a).property) (brand S a.val))

lemma accomplished : Menu (T:=fun i:I=>FC (Single (side Y (P i).1.1 (s+1))))
    (fun i x=> (Q i) (sold Y h s (P i).1.1 (composeQ Kₜ S (A i))) (replant W₀ (n i) x)):= by
  refine (Menu.total (univ:Finset (Key S)) (fun a i x=> (Q i) (Satin.knot (m i) (Typeset S a) (source S (A i) a)) (replant W₀ (n i) x)) (fun a _=> reading_knot Y h S s P A C p a)).congr ?_
  intro i x; rw [ingress_compose_sum _ _ _ _ (P i).property]; simp_rw [Finset.sum_apply]

lemma everyKey (x : I→ Key (GridStep Λ l S)): Menu (fun i t=> source W₀ (transitionL Y h S s (P i).property (A i)) (x i) t) := by
  let z(i:I)(t:PairsC):= (Q i) (sold Y h s (P i).1.1 (composeQ Kₜ S (A i))) (replant W₀ (n i) t)
  let P'(i:I):= (roomy_hosp _ (P i).property.bill.upper); let R (i:I):= selector W₀ (P' i) (x i)
  have he(i:I):source W₀ (transitionL Y h S s (P i).property (A i)) (x i)= fun t=> R i (z i t):= congrFun (transition_finance Y h S s (P i).2 (A i)) (x i)
  simp_rw [he]
  obtain ⟨p',c,u,v⟩:= accomplished Y h S s P A C p
  refine ⟨Deal.along (fun i:I=> (R i : FC (Single (n i))→ℂ)) p' ?_,c,u,fun i t=> le_trans (selector_n _ (P' i) _ _) (v i t)⟩
  intro ε t; refine ⟨ε,t,fun i a b g=>?_⟩; rw [dist_eq_norm,← map_sub]; exact lt_of_le_of_lt (selector_n _ (P' i) (x i) _) (by simpa only [←dist_eq_norm] using g)
end
private lemma SalaryPack : ∃ C:ℝ,0≤C∧∀ (v:PaidPt Y S s)(x:Catalog S), ‖transitionL Y h S s v.property x‖≤ C*‖x‖:=by
  let I:= PaidPt Y S s × (Key W₀ × {x:Catalog S // ‖x‖≤1})
  obtain ⟨C,p,t⟩:= (everyKey (I:=I) Y h S s (fun i=>i.1) (fun i=>i.2.2.1) 1 (fun i=>i.2.2.2) (fun i=>i.2.1)).budget
  let A(s':PaidPt Y S s) := transitionL Y h S s s'.property
  have ht (s':PaidPt Y S s)(x:Catalog S)(v:‖x‖≤1): ‖A s' x‖≤ C:= (catalogue_norm_le W₀ p _).mpr (fun i v'=> t (s',i,⟨x,v⟩) v')
  refine ⟨C,p,fun s' x=>?_⟩
  change ‖A s' x‖≤ _
  by_cases z:x=0; · simp [z]
  have he:= norm_pos_iff.mpr z; specialize ht s' (((‖x‖⁻¹:ℝ):ℂ) • x)
  have h0x: ‖((‖x‖⁻¹:ℝ):ℂ) • x‖=1:= by rw [norm_smul,Complex.norm_real, norm_inv, norm_norm,inv_mul_cancel₀ he.ne']
  specialize ht h0x.le; rw [map_smul,norm_smul,Complex.norm_real, norm_inv,norm_norm,← div_eq_inv_mul] at ht; exact (div_le_iff₀ he).mp ht

def salary (s:ℕ) := Classical.choose (SalaryPack Y h S s)
lemma salary_nn :0≤ salary Y h S s := (Classical.choose_spec (SalaryPack Y h S s)).1
lemma salary_en (t : PaidPt Y S s) (x:Catalog S): ‖transitionL Y h S s t.property x‖ ≤ salary Y h S s * ‖x‖:= (Classical.choose_spec (SalaryPack Y h S s)).2 t x

def transitionQ (t : PaidPt Y S s):Catalog S →L[ℂ] Catalog (GridStep Λ l S):= (transitionL Y h S s t.property).mkContinuous (salary Y h S s) (salary_en Y h S s t)
lemma transitionQ_budget (t:PaidPt Y S s) : ‖transitionQ Y h S s t‖ ≤ salary Y h S s:= LinearMap.mkContinuous_norm_le _ (salary_nn Y h S s) _
lemma transitionQ_apply (t:PaidPt Y S s)(x:Catalog S) : transitionQ Y h S s t x=transit Y h S s t.property x:=rfl
lemma sold_ticket (t:PaidPt Y S s)(x:Catalog S):
    sold Y h (s+1) t.1.1 (composeQ (tent Y h) (GridStep Λ l S) (transitionQ Y h S s t x))= ingress Y s t.1.1 t.1.2 (sold Y h s t.1.1 (composeQ (tent Y h) S x)):= exchanged Y h S s t.property x
lemma transition_ticket (P:Offered Y S s i k)(x:Catalog S): sharp Y h s i k (composeQ (tent Y h) S x)= sharp Y h (s+1) i k (composeQ (tent Y h) (GridStep Λ l S) (transitionQ Y h S s ⟨(i,k),P⟩ x)) := transition_reads ..
#print axioms sold_ticket
#print axioms transitionQ_budget
end YM.CF.Buffered.Afterglow.Hierarchy
