import YM.SU5.FiniteGaugeData.Jadot.Chor
/-! # Genuine chiral gauge wires (same fixed path), price. -/
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
namespace ProbeCode
open Reduction.Rheims
variable {N:Side}{V:Calibration}{K:Finset (Single N)}{S:Finset Cover}{X:Op (Single N)}{p h c b w t ε:ℝ}
local notation "T"=> tickA N
local notation "Ν"=> Single N
lemma rowsT (v:1≤h){A:Type*}(S:Finset A)(F:A→FC (Single N))(p:∀ i∈ S,Art h T K false (F i) c): Art h T K false (∑ i∈ S, F i) (S.card*c):=by
 classical
 induction S using Finset.induction_on with
 | empty=> simp only [sum_empty,Finset.card_empty,Nat.cast_zero,zero_mul]; exact Art.hid _
 | insert i S t ih=> rw [sum_insert t,card_insert_of_notMem t,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((_ :ℝ)*c)]; exact (p i (mem_insert_self ..)).sum (ih (fun j h=>p j (mem_insert_of_mem h))) -- Parenthesization
abbrev Fond(N:ℝ)(H:ℝ):= (2*H*H) * N^2
lemma pillar(H:1≤h)(p:Cellar K X)(t:Spear (tickA N) X)(e:‖X‖≤ b)(w':K.card≤w) : Art h (tickA N) K false (dg X) (Fond w h * b):=by
 let F(i j:Ν):= X i j • (put i*takeF j); have hp(F':ℂ):0≤‖F'‖:= norm_nonneg _; have hv:0≤b:= (norm_nonneg _).trans e
 let k := h* (1:ℝ); have hk:(2:ℝ)* h≥0:=by linarith
 unfold dg dyad; change Art _ _ _ _ (∑ i:Ν,∑ j:Ν,F i j) _
 let f(i):=∑ j∈ K,F i j; let K₀:= Tset N
 have he (i j:Ν)(k:X i j≠0): i∈ K∧ j∈K ∧ i∈K₀∧ j∉K₀:=by
    have he (S:Finset Ν)(h:cutM S * X=X):i∈ S := by by_contra v; apply k; nth_rw 1 [←h]; rw [cutM,Matrix.diagonal_mul,if_neg v,zero_mul] -- tune
    have hx(S:Finset Ν)(h:X*cutM S=X): j∈ S:=by by_contra v; apply k; nth_rw 1 [←h]; rw [cutM,Matrix.mul_diagonal,if_neg v,mul_zero] -- tune
    exact ⟨he _ p.leftP,hx _ p.rightP,he _ (touchP N ▸ t.up),mem_compl.mp (hx _ (by rw [dim_cut]; exact (touchP N) ▸ t.low))⟩
 have hl:∑ i:Ν,∑ j:Ν,F i j= ∑ i∈K,f i:=by
    have hi(i:Ν): ∑ j:Ν,F i j=f i:=by refine (sum_subset (subset_univ K) ?_).symm; intro j v l; unfold F; rw [not_not.mp (mt (fun k=> (he i j k).2.1) l),zero_smul] -- tune not_not ?
    simp_rw [hi]; apply (sum_subset (subset_univ K) ?_).symm; intro i v l; unfold f; exact sum_eq_zero fun j t'=>by unfold F; rw [not_not.mp (mt (fun k=> (he i j k).1) l),zero_smul]
 rw [hl]; refine (rowsT H K (c:=K.card*(b*(2*h*h))) f (fun i x=> rowsT H K (F i) (fun j e'=>?_))).pump ?_
 · by_cases v: X i j=0
   · unfold F; rw [v,zero_smul]; exact (Art.hid _).pump (by positivity)
   obtain ⟨p,q,k,h_⟩:= he _ _ v; unfold F; have hu:Upt T (basisKet i):= by rw [touchP]; exact within_basis _ _ k; -- tune
   have hz:Upt (1-T) (basisKet j):= by rw [touchP,← dim_cut]; exact within_basis _ _ (mem_compl.mpr h_)
   have hy: Art h T K false (put i*takeF j) (2*h*h):=by
      let X:= Art.work (Art.chor (h:=h) _ hu (within_basis K _ p)) (Art.thal _ hz (within_basis K _ q)); rw [←create_put,←remove_take]; exact (X.pump (by simp [basisKet])) -- specify Ram within

   exact (Art.scale _ hy).pump (mul_le_mul_of_nonneg_right ((norm_entry ..).trans e) (by positivity))
 · unfold Fond; have hw: (K.card:ℝ)^2≤w^2 := pow_le_pow_left₀ (by positivity) w' 2; nlinarith only [mul_le_mul_of_nonneg_left hw (mul_nonneg hv (show 0≤ 2*h*h from by positivity))]
-- API positive analytic Mark
open Reduction.Rheims
lemma pay_chisel(W: Desire V S)(l:forall (N:Side)(U:Pane N), Spear (tickA N) (W.print N U)): Auth V S W.paid (fun N U=> dg (W.print N U)):=by
 let D:= W.print; let w:ℝ:= investK S.card; have hw:0≤w:=Nat.cast_nonneg _; have hy(N:Side): ((modesIn N (region S N)).card:ℝ) ≤ w:=Nat.cast_le.mpr (seatCard S N); let a:=W.owed
 refine ⟨W.at_site, W.ticket, W.fits,fun N u X=> by rw [W.gauge, dg_cov], fun H p=>?_,fun H p ε e=>?_⟩
 · have hv:0<H:=lt_of_lt_of_le zero_lt_one p; let c:= Fond w H*a; have hc:0<a:= W.hv; have h0:0≤c:=by unfold c Fond; positivity
   exact ⟨c+1,by linarith,fun N U=> (pillar p (W.col N U) (l N U) (W.price N U) (hy N)).pump (le_add_of_nonneg_right zero_le_one)⟩
 let K:= Fond w H; have hu:0≤K:=by unfold K Fond; positivity
 let t:= ε/(K+1); have hp:0<K+1:=by linarith
 have ht:0<t:=div_pos e hp; obtain ⟨s,v,L⟩:= W.melt t ht; refine ⟨s,v,fun N U hx=>?_⟩; let X:= D N U-D N 1; rw [show dg (W.print N U)-dg (W.print N 1)=dg X by unfold X D; rw [sub_eq_add_neg,sub_eq_add_neg,dg_add,dg_neg]]; refine (pillar p ?_ ?_ (L N U hx) (hy N)).pump ?_
 · constructor; · rw [_root_.mul_sub,(W.col N U).leftP,(W.col N 1).leftP]
   rw [_root_.sub_mul,(W.col N U).rightP,(W.col N 1).rightP]
 · exact ⟨by rw [_root_.mul_sub,(l N U).up,(l N 1).up],by rw [_root_.sub_mul,(l N U).low,(l N 1).low]⟩
 · exact ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ht.le)).trans_eq (by change (K+1)*t=_; unfold t; field_simp)
open Niagara
variable (X:Niagara.Chisel)
lemma shoe (X:Niagara.Chisel)(U:Pane N) : Spear (tickA N) (X.buyD N U):=by
 let A:= X.upCard N; let B:= X.downCard N; let S:= X.surfN U; rw [touchP N]; let K:=Tset N; have h:Spear (cutM K) S:=by
    constructor
    · ext ⟨x,i⟩ ⟨y,j⟩; unfold cutM; rw [Matrix.diagonal_mul]; by_cases hp:x=X.upCard N ∧ y=X.downCard N; · rw [hp.1,if_pos ?_,one_mul]; exact (grade_one ..).2 X.up
      simp [S,Chisel.surfN,Tulip.panel, hp]
    rw [←dim_cut]; ext ⟨x,i⟩ ⟨y,j⟩; unfold cutM; rw [Matrix.mul_diagonal]; by_cases hp:x=X.upCard N ∧ y=X.downCard N; · rw [hp.2,if_pos ?_,mul_one]; exact mem_compl.mpr (mt (grade_one ..|>.1) X.dn)
    simp [S,Chisel.surfN,Tulip.panel,hp]
 change Spear (cutM K) (_ • S); exact ⟨by rw [Algebra.mul_smul_comm,h.up], by rw [Algebra.smul_mul_assoc,h.low]⟩
abbrev score (X:Niagara.Chisel): Paint:= fun N U=> dg (X.buyD N U)
lemma Country (V:Calibration)(X:Niagara.Chisel) : Auth V X.town (X.DesireB V).paid (score X):= pay_chisel (X.DesireB V) fun N U=>shoe X U
end ProbeCode
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
