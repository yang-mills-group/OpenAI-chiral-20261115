import GaugeFieldConstruction.Maiola
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(o:Seat n)(M:Male)
open Spectrix
-- Lin_H on ℝ component maps
private def floraL : yardLot →ₗ[ℝ] Paper n where
 toFun:=Flourish o
 map_add' i j:=by
    unfold Flourish Pyl; rw [←sum_add_distrib]; apply sum_congr rfl; intro k _; let I:=fun _:Pane n=> i k; let J:=fun _:Pane n=>j k; exact Eq.trans (congrArg (fun f:hart_X n=>plac f true) (beam_add o k I J 1)) ((plac_ψ _ _ 0).1)
 map_smul' a x:=by
    unfold Flourish Pyl; rw [RingHom.id_apply,smul_sum]; exact sum_congr rfl fun i _=>by exact Eq.trans (congrArg (fun f:hart_X n=> plac f true) (beam_scale o i (fun _=>x i) a 1)) ((plac_ψ _ 0 a).2)
-- use Pal-instance.
private lemma carve_S (A: ComG→L[ℝ] Pal)(v:ℝ): Carved o (v • A)=v • Carved o A:=by
 unfold Carved; rw [smul_comm v]; apply congrArg (mindChart.threshold • ·); rw [smul_sum]; apply sum_congr rfl; intro i _; rw [show mallet o (v • A) mindChart i=v • mallet o A mindChart i from rfl,beam_scale,(plac_ψ _ 0 v).2] -- tune Norm ambigu
private def carveL : (ComG→L[ℝ]Pal) →ₗ[ℝ]Paper n where
 toFun:=Carved o
 map_add' i j:=by
    unfold Carved; rw [←smul_add,←sum_add_distrib]; apply congrArg (mindChart.threshold • ·); apply sum_congr rfl; intro k _; rw [mallet_H o _ i j,beam_add,(plac_ψ _ _ 1).1]
 map_smul' v A:= carve_S o A v
private abbrev LushV:= (leadF Gem Gem) × (leadF Gem Sut)
private def gripsL : LushV →ₗ[ℝ]Paper n where
 toFun x:= GripsO o x.1 x.2
 map_add' l j:=by
    unfold GripsO CoverP Silex; rw [←smul_add]; apply congrArg (mindChart.threshold^2 • ·); funext i U; cases i with
    | none=> let H(k:LushV):= bloomT k.1 k.2; change terrace o _ (H (l+j)) U= terrace _ _ (H l) _ + terrace _ _ (H j) _; unfold terrace; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; unfold νt ψTile; simp only [H,bloom_apply,mono_apply,Prod.fst_add,Prod.snd_add, ContinuousLinearMap.add_apply]; ring -- try
    | some v=> simp [isolate]
 map_smul' v l:=by
    unfold GripsO CoverP Silex; rw [RingHom.id_apply,smul_comm v]; apply congrArg (mindChart.threshold^2 • ·); funext i U; cases i with
    | none=> let H(k:LushV):= bloomT k.1 k.2; change terrace o mindChart (H (v • l)) U=v • terrace _ mindChart (H l) U; unfold terrace; rw [smul_sum]; apply sum_congr rfl; intro i _; unfold νt ψTile; simp only [H,bloom_apply,mono_apply,Prod.smul_fst,Prod.smul_snd, ContinuousLinearMap.smul_apply,Complex.real_smul]; ring -- tune
    | some v=> simp [isolate]
variable {W:Waves}
-- vanish Booleans
private lemma OleZeroK {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] : CostOle (show Ole E F from (0,0,0))=0:=by change ‖(0: Ole E F)‖=0; exact @norm_zero (Ole E F) _
private lemma OleZeroH : CostOle (show PalOne from (0,0,0))=0:= OleZeroK (E:=Views) (F:=Pal)
lemma chart_zero (V:chartF W=(0,0,0))(p:BudgetPoint)(w:20<n.val): αPureX o M p W=0:=by
 apply norm_eq_zero.mp ; refine le_antisymm ?_ (norm_nonneg _); unfold αPureX; let h:=Cushion (M:=M) o (chartF W) w; rw [V] at h ⊢; exact (h.trans (show QuiltB*CostOle (show PalOne from (0,0,0))≤ 0 by
    rw [show CostOle (show PalOne from (0,0,0))=0 from OleZeroH,mul_zero])) 
lemma busC_nil(V:(bF4 W).val=0)(Z:bF5 W=0)(p: BudgetPoint)(h:ℝ):busC o M h p W=0:=by
 unfold busC CoverP; rw [V,Z, show bloomT 0 0=0 from ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=> (bloom_apply ..).trans (show (0:ℂ)+(0+0)=0 by ring),show terrace o p 0=0 from funext fun u=>by simp [terrace,ψTile,νt,mono_apply]]; simp [Silex,isolate]
lemma busF_nil(V:chartF W=(0,0,0))(p:BudgetPoint)(r:h≠0)(w:20<n.val):busF (h:=h) (p:=p) (o:=o) M W=0:=by
 let L:=busF (h:=h) (p:=p) (o:=o) M W; have he:(h^2:ℝ) • L=0:=by unfold L; rw [bus_root M W r,chart_zero]; exact (map_zero (floraL o)); exact V; exact w -- order
 exact (smul_eq_zero.mp he).resolve_left (pow_ne_zero _ r)
lemma Guide_nil (W:Waves)(u:Genre.gauge.Room W)(t:0<h)(P:p.power≤3)(L:p.order≤6)(w:20<n.val):αGuide o M p W h=0:=by
 let X:= αPureX o M p W; let K:= landA M o (αPure o M p W h) p h; have he:αPure o M p W h=0:=by
    unfold αPure; rw [chart_zero o M u.1 _ w]; unfold blurred; apply sum_eq_zero; intro i _; funext V; change pulseH (beamer o i (fun _=>0) h V)=0; rw [show beamer o i _ h V=0 from (show beamer o i (fun _=>0) h V=0 from ?_)]; exact (by have hp:= pulse_add (n:=n) 0 0; rw [add_zero] at hp; let Z:= pulseH (0:Op (Single n)); exact add_left_cancel (a:=Z) (hp.symm.trans (add_zero _).symm)) -- revise
    ext j k; simp [beamer,carryU,modelK,Moto.seed_k] -- tune
 unfold αGuide; rw [u.2,he]; let F:=linearØ (h:=h) (p:=p) o M 0; have hp:(fun _:Pane n=>hollow (n:=LeanV (Single n)) (0:ℂ))=(0:InkD n):=funext fun i=>Subtype.ext (zero_smul ..)
 rw [hp] at F; rw [show landA M o 0 p h=0 from F.mixed.symm]; exact (show ∀{E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](L:E→L[ℝ] F), L-0=L from fun {_ _} _ _ _ _ _=> sub_zero _) (0:ComG→L[ℝ] Pal)
lemma busG_nil (W:Waves)(u:Genre.gauge.Room W)(t:0<h)(P:p.power≤3)(L:p.order≤6)(w:20<n.val): busG o M p h W=0:=by
 have he:(h^2*p.threshold) • busG o M p h W=0:=by rw [show (h^2*p.threshold) • busG o M p h W= Carved o (αGuide o M p W h) from bus_Srail M W t.ne',Guide_nil o M W u t P L w]; exact map_zero (carveL o) -- tune o explicit arg
 exact (smul_eq_zero.mp he).resolve_left (mul_ne_zero (pow_ne_zero _ t.ne') p.threshold_pos.ne')
-- shapes
abbrev coat_A (V:Genre)(K:ℝ):Set (Paper n):= {F| ∃ (W:Waves)(p:BudgetPoint)(M:Male)(h:ℝ),‖W‖≤K ∧ V.Room W ∧ p.power ≤3∧p.order ≤6∧0<h∧ F=V.coinB p h • Bush o M p h W}
private lemma tons_b {X F:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ X][FiniteDimensional ℝ F] (C:ℝ) : Odious {A:X→L[ℝ]F| tautF A ≤ C}:= odor C
private lemma tons_k {X F G:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G][FiniteDimensional ℝ X][FiniteDimensional ℝ F][FiniteDimensional ℝ G](C:ℝ)(L: ((X→L[ℝ]F) × (X→L[ℝ]G))→ₗ[ℝ]Paper n)(S:Set (Paper n))(H:∀ i∈S,∃ l:(X→L[ℝ]F)× (X→L[ℝ]G), max (tautF l.1) (tautF l.2)≤ C∧i=L l): Odious S:=by
 apply Od_L (T:={l:(X→L[ℝ]F) × (X→L[ℝ] G)| max (tautF l.1) (tautF l.2) ≤ C}) L _ (odor C)
 rintro i v; obtain ⟨l,u,rfl⟩:= H i v; exact ⟨l,u,rfl⟩
private lemma torC (k:ℝ)(S:Set (Paper n))(u: ∀ i∈S,∃ l:LushV, max (tautF l.1) (tautF l.2)≤ k∧i=gripsL o l):Odious S:=tons_k (X:=Gem) (F:=Gem→L[ℝ]ℂ) (G:=Sut→L[ℝ]ℂ) k _ S u
lemma wool (U:Genre)(K:ℝ)(w:20<n.val):Odious (coat_A o U K):=by
 let E:= |QuiltB| *K; let S:= |zenMaze| *K; let C:=|κzone| *K
 let X: Set (Paper n):={Y|∃ i:yardLot, fena i ≤ E ∧ Y=Flourish o i}
 let F(V:ℝ): Set (Paper n):={Y|∃ i:ComG→L[ℝ]Pal,tautF i ≤ V ∧ Y=Carved o i}
 have hp:Odious X:=by apply Od_L (floraL o) _ (odor (V:=yardLot) E); rintro i ⟨j,w,rfl⟩; exact ⟨j,w,rfl⟩ -- ambiguity Pal product
 have hr(M:ℝ) : Odious (F M):=by apply Od_L (carveL o) _ (tons_b (X:=ComG) (F:=Pal) M); rintro i ⟨j,w,rfl⟩; exact ⟨j,w,rfl⟩
 cases U
 · apply Od_a _ hp (hr S); rintro x ⟨W,p,M,h,e,u,h0,h1,h2,rfl⟩; let V:= αPureX o M p W; let L:=αGuide o M p W h; let A:=p.threshold⁻¹ • L
   refine ⟨Flourish o V,⟨V,?_,rfl⟩, Carved o A,⟨A,?_,rfl⟩,?_⟩
   · exact (Cushion (M:=M) o (chartF W) w).trans (mul_le_mul (le_abs_self _) (bean_G W K e).1 (Ole_non _) (abs_nonneg _))
   · have ht:=clock_mismatch o M h2 W h0 h1 w; rw [u.2.2, show αGuide o M p W h-0= L from ContinuousLinearMap.ext fun i=> (show ∀ {E:Type}[NormedAddCommGroup E](x:E), x-0=x from fun {_} _ _=> sub_zero _) (L i)] at ht; change tautF (p.threshold⁻¹ • L)≤ _; rw [show tautF (p.threshold⁻¹ • L)=|p.threshold⁻¹| * tautF L from (show ∀{E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](a:ℝ)(f:E→L[ℝ]F), tautF (a • f)= |a| *tautF f from fun {_ _} _ _ _ _ a f=> norm_smul ..) _ _]
     rw [abs_of_nonneg (inv_pos.mpr p.threshold_pos).le]; refine (mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) p.threshold_pos.le) e (norm_nonneg _) (mul_nonneg (abs_nonneg _) p.threshold_pos.le))) (inv_pos.mpr p.threshold_pos).le).trans_eq ?_; field_simp [p.threshold_pos.ne']; ring
   unfold Genre.coinB Bush; simp only [reduceCtorEq, ↓reduceIte, Genre.orderB, pow_zero,mul_one,busC_nil o M u.1 u.2.1,zero_add,smul_add]; rw [bus_root M W h2.ne',show Carved o A=_ from carve_S ..,← (show _ • busG o M p h W=Carved o L from bus_Srail M W h2.ne'), smul_smul, show p.threshold⁻¹*(h^2*p.threshold)=h^2 from ?_] -- tune order
   rw [mul_comm _ p.threshold, ← mul_assoc,inv_mul_cancel₀ p.threshold_pos.ne',one_mul]
 · apply Od_sub _ (hr C); rintro i ⟨W,p,M,h,e,u,h0,h1,h2,rfl⟩; let A:=αGuide o M p W h; refine ⟨A, (entrust_M o M h2 W h0 h1 w).trans (mul_le_mul (le_abs_self _) e (norm_nonneg _) (abs_nonneg _)),?_⟩; unfold Bush Genre.coinB; rw [busC_nil o M u.1 u.2.1 p h,busF_nil o M u.2.2 p h2.ne' w,zero_add,zero_add]; simpa only [reduceCtorEq,↓reduceIte,Genre.orderB,pow_one] using (show (h^2*p.threshold) • busG o M p h W=Carved o A from bus_Srail M W h2.ne') -- precedence tune
 apply torC o K; rintro i ⟨W,p,M,h,e,u,h0,h1,h2,rfl⟩; let V:LushV:=((bF4 W).val,bF5 W); have he:= bean_G W K e; refine ⟨V,max_le he.2.1 he.2.2.1,?_⟩; unfold Bush; rw [busF_nil o M u.1 p h2.ne' w, busG_nil o M W u h2 h0 h1 w,add_zero,add_zero]; unfold Genre.coinB; simp only [ite_true,one_mul,Genre.orderB]; exact recipeC (o:=o) p mindChart _ _ -- o explicit
end ArtCart
end MastTin
end YM.CF.XGarden
end
