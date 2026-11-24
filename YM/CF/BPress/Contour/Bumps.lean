import YM.CF.BPress.Contour.Proof
/-! VolumeB-poly lemma:B-contour, block thresholds, used finite torus version of written proof (indeed uniform). Count via tree prices rather than spelling walk bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Push.SectorMeasure Env Finset MeasureTheory Function Palmer Ledger Grid Branch Bands Locale Lattice
open scoped Classical Topology BigOperators
variable {s:Side}{b:BandWidth}(X:Bands s b)(R:Hangar s)(r:ℕ)
def coverB := (4*r+1)^4
def lavish (r:ℕ):ℝ := (1/262144)/(coverB r :ℝ)/Real.exp (8*(coverB r :ℝ))
lemma coverB_pos : 0 < coverB r:=by unfold coverB; positivity
lemma lavish_pos : 0 < lavish r := by have h:= coverB_pos r; unfold lavish; positivity
lemma city : Cash (Gilt X R r) (fun _=>lavish r) (4+4) (1/262144):=by
 let F:=shape X R; let N(i):=Gilt X R r i; have ht:= lavish_pos r; let L:= Real.exp (8*(coverB r:ℝ))*lavish r; refine ⟨fun i=>ht.le,fun x=>⟨fun i=>?_, (hasSum_fintype _).summable,?_⟩⟩; · unfold score; split; positivity; rfl
 rw [tsum_fintype]; let u:=N x; have hx: 0≤L:=mul_nonneg (Real.exp_pos _).le ht.le; have he(i):x∈N i ↔ i∈ u:=by simp only [N,u,Gilt, bay_mem,(shape X R).sym x i]; -- tune
 have hp : (∑ i:SiteX X R, if i∈u then L else 0)=u.card*L:= by rw [←sum_filter,filter_mem_eq_inter, univ_inter, sum_const,nsmul_eq_mul]
 refine (sum_le_sum (g:=fun i=>if i∈u then L else 0) (fun i _=>?_)).trans ?_
 · unfold score; split; next q=> rw [if_pos ((he i).mp q)]; unfold L; gcongr; norm_num; exact capacity .. -- tune
   · exact ite_nonneg hx le_rfl
 rw [hp]; apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show u.card≤coverB r from capacity ..)) hx); unfold L lavish; have H:0<(coverB r:ℝ):= Nat.cast_pos.mpr (coverB_pos r); exact le_of_eq (by field_simp)
variable {X R} {I:Type}{Φ:SiteX X R→ Type*}[DecidableEq I][Fintype I][∀ i,MeasurableSpace (Φ i)][∀ i,Nonempty (Φ i)]
variable {T:I→Finset (SiteX X R)} {A:(Seal (SiteX X R))→ I→ (∀ i,Φ i)→ℂ}{G:Seal (SiteX X R)→(∀ i,Φ i)→ℂ}
variable {μ ν:∀ i, Measure (Φ i)}[∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)] {a:I→ℝ}
lemma contour (v:Holds (Gilt X R r) T A G μ ν a (lavish r))(t: Cash T a 4 (1/16384))(p:evenT (shape X R) T) : Real.exp (-(Fintype.card (SiteX X R):ℝ))≤ ‖glob (Gilt X R r) A G μ ν‖:=by
 let Z:= Gilt X R r; let F:=shape X R; let m:Side:=16; have u:= lavish_pos r|>.le; have hu(i:I):a i≤1:= (t.single (by norm_num) _ (inhabited_grove (p i))).trans (by norm_num); have hx: Stakes m 4 (1/262144):=⟨by norm_num,by norm_num,by norm_num [m]⟩
 have ht : evenT F Z:=fun i=> body_bay X R i r; have hp:= bill_core ht (folio X R) hx u (city X R r); have hw:= cash_beads hp (t.scale 2 (by norm_num)); refine modulus (u:=1) (C:=1/128) (γ:=1/4096) (v.sum u hu) (own_gilt X R r) ⟨by norm_num,by norm_num,by norm_num⟩ ⟨by norm_num,by norm_num,by norm_num⟩ (by norm_num [till_cost]) (by norm_num [till_cost]) (folio X R) ht p (hw.chill (by norm_num)|>.weaken (by norm_num [till_cost])) -- tune
end YM.CF.BPress.Contour
#print axioms YM.CF.BPress.Contour.contour
