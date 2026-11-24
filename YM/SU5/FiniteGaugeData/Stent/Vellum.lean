import YM.SU5.FiniteGaugeData.Stent.Velcro
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
variable {N:Side}(R:Patch)(L:4≤R.L.val)(H:Hosp (fieldQ R.L) N)
local notation "η"=> nodeC (specialM R.L)
local notation "E₁"=> Edge (Seat N)
abbrev drawE (N:Side)(x:Cover)(i:Axis):= ((wrap (More N)) x,i)
abbrev knee (R:Patch)(N:Side): Edge (Seat N):= drawE N (nodeC (specialM R.L)-step 0) 0
noncomputable def lottery (R:Patch)(u:SU.E)(W:Pane N): Pane N:= Function.update W (knee R N) (W (knee R N)*u⁻¹)
private abbrev fur (i:Axis):Cover:=step i
local notation "δ" i:max=> (step i : Cover)
local notation "f" x:max=> wrap (More N) x
local notation "K"=> fieldQ R.L
lemma horiz(U:Pane N)(i j:Axis): doorG R (stairW i j) (onC N U) = (U (drawE N (η-step i) i))⁻¹*((U (drawE N (η-step i-step i) i))⁻¹*((U (drawE N (η-step i-step i-step j) j))⁻¹ * (U (drawE N (η-step i-step i-step j-step j) j))⁻¹)):=by
 unfold doorG stairW; simp [travel,onC,expandAt,drawE,sub_eq_add_neg] -- tune
include H L
set_option linter.unusedSimpArgs false in
lemma pivoting (u:SU.E)(U:Pane N): SpanM R (onC N (lottery R u U))=u* SpanM R (onC N U):=by
 let a:= δ 0; let b:= δ 1; let x:= η -a; let y:=η-b-b-a; let V:= lottery R u U; let T:=knee R N; let G:Ratio (1:Side) R.L:= ⟨R.L,by simp⟩; have hz: (visits η dogwalk).toFinset⊆ K:=dog_p ▸ forge G R.odd_side L 1; have hv: (visits η birdwalk).toFinset⊆ K:=bird_p ▸ forge G R.odd_side L (Equiv.swap (0:Axis) 1);
 have hp:x∈ K:= hz (by simp [dogwalk,stairW,visits,x,a, sub_eq_add_neg]); have hh:x-a∈ K:=hz (by simp [dogwalk,stairW,visits,x,a,sub_eq_add_neg]); have hy:y∈ K:= hv (by simp [birdwalk,stairW,visits,y,a,b,sub_eq_add_neg]); have he:y-a∈ K:=hv (by simp [birdwalk,stairW,visits,y,a,b,sub_eq_add_neg]);
 have h₁(p:E₁)(hx:p≠T):lottery R u U p=U p:= update_of_ne hx ..; have h₄:V T= U T * u⁻¹:= by unfold V lottery T; simp only [update_self]
 have q₁(z:Cover): drawE N z 1≠T:= fun i=> (by decide:(1:Axis)≠0) (congrArg Prod.snd i)
 have q₂(z:Cover)(t:z∈K)(e:z≠x): drawE N z 0 ≠ knee R N:= fun i=>e (H.seat_ t hp (congrArg (fun s:E₁=> s.1) i))
 have Q₁: x-a≠x:=fun i=>by have h:= congrFun (sub_eq_self.mp i) (0:Axis); -- maybe sub_eq_self name?
                           norm_num [a] at h
 have Q₂: y≠ x:=fun i=>by have e:=congrFun i (1:Axis); simp only [y,x,a,b,Pi.sub_apply, step_apply] at e; norm_num [show (1:Axis)≠0 from by decide] at e; omega
 have Q₃:y-a≠x:= fun i=>by have e:=congrFun i (1:Axis); simp only [y,x,a,b,Pi.sub_apply,step_apply] at e; norm_num [show (1:Axis)≠0 from by decide] at e; omega
 unfold SpanM dogwalk birdwalk; simp_rw [horiz]
 rw [show lottery R u U (drawE N (η-step 0) 0)=_ from h₄]; simp_rw [show ∀ z:Cover,lottery R u U (drawE N z 1)=U (drawE N z 1) from fun z=>h₁ _ (q₁ z)]; rw [h₁ _ (q₂ _ hh Q₁),h₁ _ (q₂ _ hy Q₂), h₁ _ (q₂ _ he Q₃)]; unfold T knee x y a b; rw [mul_inv_rev,inv_inv]; simp only [mul_assoc] -- maybe group hold. 
local notation "μ"=> SU.group.probHaar
local notation "νᵢ"=> Wilson.prior SU.group (More N)
lemma editorial (c:ℂ):∀ᵐ x∂Wilson.prior SU.group (More N), Nylon R (onC N x)≠c:=by
 let x:= More N; let V:= lottery R (N:=N); let T:= knee R N
 let Q(W':Pane N):= Nylon R (onC N W'); have hx:MeasurableSet {x:SU.E×Pane N| Q (V x.1 x.2)≠c}:= (show Continuous (fun i:SU.E×Pane N=>Q (V i.1 i.2)) from ((Nylon.cont R).comp (on_cont N)).comp ?_).measurable (measurableSet_singleton _).compl; swap
 · apply continuous_pi; intro i; unfold V lottery; by_cases p:i=knee R N
   · simp_rw [p,update_self]; fun_prop -- indentation
   simp_rw [Function.update_of_ne p]; fun_prop
 have hv(i:Pane N):∀ᵐ u∂μ,Q (V u i)≠c:=by unfold V Q; simp_rw [officials,pivoting R L H]; let Z:= SpanM R (onC N i); exact (measurePreserving_mul_right μ Z).quasiMeasurePreserving.ae (p:=fun y:SU.E=> CashNotch y ≠ c) (WidePay c)
 have hp(u:SU.E):MeasurePreserving (V u) νᵢ νᵢ:= by
    apply Fixed.Pivots.update_preserve; · exact (measurable_pi_apply _).mul measurable_const
    intro i; simp_rw [Function.update_self]; exact measurePreserving_mul_right μ u⁻¹
 obtain ⟨v,h⟩:= ((Measure.ae_ae_comm (p:=fun u y=> Q (V u y)≠c) («μ»:=μ) («ν»:=νᵢ) hx).mpr (Eventually.of_forall hv)).exists; filter_upwards [(hp v⁻¹).quasiMeasurePreserving.ae h] with W p; have ht: V v (V v⁻¹ W)= W:=by funext i; unfold V lottery; by_cases p:i=knee R N <;> simp [p, Function.update_of_ne]
 exact ht ▸ p
#print axioms editorial
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
