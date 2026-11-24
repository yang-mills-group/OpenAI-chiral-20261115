import GaugeFieldConstruction.Synod
/- GE inscription full prior gauge average. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 90000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d t r u c h a b h0:ℝ}{j k:ℕ}{m B n:Side}
namespace MastTin
open Shield Echo Ledger Jet
local notation "GS"=> SU.group
local notation "Λ"=> CSide m B
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable {p:BudgetPoint}{A:Paper n} (o:Seat n) {U V:Hubber n} {N: Paper n}
section mul
variable (F:Pane n→ℝ)
abbrev hires (A:Paper n): Paper n:=fun j i=> F i • A j i
def BridV (X:Flounces n):Flounces n:= ∑ i:Hubber n, show Flounces n from Pi.single (i∪Pach o) (hires F (X i))
lemma costH (p':TrackD p V h A c)(q:Micro p V F t): TrackD p V h (hires F A) (2^p.order*t*c):=by
 obtain ⟨V,H,k⟩:=p'; refine ⟨fun i=>2^p.order*t*V i,fun i=>⟨micro_m F (F:=A i) q (H i).1,fun v=>?_⟩,?_⟩
 · unfold hires; simp_rw [(H i).2 v]; funext; simp
 simp_rw [mul_left_comm (papW _ _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left k (mul_nonneg (by positivity) q.1)
lemma upMark(Q: Paper n)(A:Pane n):marketD (hires F Q) A= F A • marketD Q A:=by unfold marketD; rw [smul_sum]; apply sum_congr rfl; intro i _; exact smul_assoc ..
private lemma fitDockX(D:Dock o V): Dock o (V∪Pach o):=by
 have hp:Grove (Tenant.terr _) (Pach o):= crown_H (.single o) _
 exact ⟨mem_union_left _ D.1,D.2.unite hp D.1 (halo_subset _ _ (mem_singleton_self _))⟩
abbrev ρZ (a:ℝ):= Real.exp (a*((49:ℝ)^4))
private lemma token_R (p:0≤a):rent a (Pach o) ≤ ρZ a:=Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast (show (Pach o).card≤49^4 from (by simpa [Pach] using Corona.halo_size ({o}:Support (More n)) 24))) p)
lemma BrideH (X: Flounces n)(p':TraceD p o h a X c)(q:Micro p (Pach o) F t)(w:0≤a): TraceD p o h a (BridV o F X) (ρZ a*(2^p.order*t*c)):=by
 obtain ⟨V,P,s⟩:=p'; apply trace_p (trace_sum (p:=p) (h:=h) univ (fun i:Hubber n=> Pi.single (i∪Pach o) (hires F (X i)):Hubber n→ Flounces n) (fun i=> rent a (i∪Pach o)*(2^p.order*t*V i)) fun i _=>?_) le_rfl
 · let T:= 2^p.order*t; have hT:0≤T:=mul_nonneg (by positivity) q.1; refine le_trans (sum_le_sum (g:=fun i=> ρZ a * (T * (rent a i*V i))) fun i _=>?_) ?_
   swap; · simp_rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s hT) (Real.exp_pos _).le
   have hD:rent a (i∪Pach o) ≤rent a i*ρZ a:=(rent_join _ _ w).trans (mul_le_mul_of_nonneg_left (token_R o w) (Real.exp_pos _).le) -- name tune
   exact (mul_le_mul_of_nonneg_right hD (mul_nonneg hT (track_pos (P i).1))).trans_eq (by unfold T; ring)
 by_cases D: Dock o i; · exact explore o (fitDockX o D) (costH F (track_o (P i).1 subset_union_left) (micro_spin q subset_union_right))
 rw [(P i).2 D, show hires F 0=0 from funext fun j=>funext fun i=>by simp [hires],Pi.single_zero]
 exact trace_p trace_Z le_rfl (mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (by positivity) q.1) (track_pos (P i).1)))
lemma report_S{I:Type}[Fintype I](A:I→Flounces n) : totalE o (∑ i,A i)=∑ i,totalE o (A i):=by
 unfold totalE; rw [show letter _=_ from (show letter (∑ i,A i)=∑ i,letter (A i) from ?_),conn_X]; unfold letter; simp_rw [Finset.sum_apply]; rw [sum_comm]
lemma report_H(X:Flounces n)(U:Pane n): totalE o (BridV o F X) U= F U • totalE o X U:=by
 unfold BridV; rw [report_S o,Finset.sum_apply]; unfold totalE; simp_rw [show ∀ i:Hubber n,marketD (letter (show Flounces n from Pi.single (i ∪ Pach o) (hires F (X i))))= marketD (hires F (X i)) from fun i=>roots_dist ..]; rw [letter,conn_X,Finset.sum_apply,smul_sum]; exact sum_congr rfl fun i _=>upMark F (X i) U
end mul
open TableF TableF.Lenten Haro Housing HushP
abbrev Gval(o:Seat n)(f:PlaqAxes)(p:BudgetPoint)(q:Clip)(x:ℝ)(l:Axis):Lit n:= markFee o q l f p x
abbrev GDecr(o:Seat n)(p:BudgetPoint)(l:Axis)(f:PlaqAxes)(x:ℝ)(j:inkMus)(U:Pane n):ℝ:= -(dimeT o l f p x j U*Turret o p.threshold U)
lemma marks_budget(q:Clip):∃ C D:ℝ,0≤C∧0≤D∧∀ {n:Side}(o:Seat n)(l:Axis)(f:PlaqAxes)(p:BudgetPoint)(x:ℝ),0<x→1≤x*p.threshold^2→p.order≤6→p.power≤3→
 Micro p (Pach o) (Gval o f p q x l) C∧∀ i:inkMus, Micro p (Pach o) (GDecr o p l f x i) (D/(x*p.threshold)):=by
 obtain ⟨v,hv,H⟩:=F_grade; obtain ⟨R,Y,hU,q',k⟩:= armCap 7 q; let a:=‖Complex.ofRealCLM‖; let b:= (2:ℝ)^6; refine ⟨a*(R*(1+b*Y))*b*v, b*v*R*‖ContinuousLinearMap.mul ℝ ℝ‖,by have hz:=zero_le_one.trans hv; unfold a b; positivity,by have hz:=zero_le_one.trans hv; unfold b; positivity,@fun n o l f p x hp t s u=>?_⟩; let Q:=Gval o f p q x l; let t':= p.threshold; let V:=Lamp o l f p; have e:0<t':=p.threshold_pos; let L:= Turret o t' (G:=GS); have h:=H n o (KitP l f) p u s
 have hF(i: Pane n)(p':pingS p.threshold (Pach o) i):Allows p.order (Q ∘ Shield.solo p.threshold i) 0 (a*(R*(1+b*Y))*b*v):=by
     obtain ⟨g,r⟩:= k p.threshold e p.threshold_le o i p'; exact milk_core o q l f p x _ (zero_le_one.trans hv) h i p' _ _ hU (g.order (Nat.succ_le_succ s)) (r.order (Nat.succ_le_succ s)) s hp t
 refine ⟨⟨(hF 1 (ping_f p _)).nonneg,Env.compact (continuous_iff_continuousAt.mpr fun i=> lively i (mark_jet o q l f p x i).continuousAt),mark_local o q l f p x,hF⟩,fun j=>?_⟩
 let T:= L; let D:=b*v*R*‖ContinuousLinearMap.mul ℝ ℝ‖; let K(U:Pane n):= dimeT o l f p x j U
 have J(U:Pane n)(w:pingS t' (Pach o) U): Allows p.order (GDecr o p l f x j ∘ Shield.solo p.threshold U) 0 (D/(x*t')):=by
     let M:= Shield.solo t' U; let G:EuclideanSpace ℝ inkMus→L[ℝ]ℝ:= PiLp.proj 2 (fun _:inkMus=> ℝ) j; let Q:= G ∘L LeadK.repr.toContinuousLinearEquiv.toContinuousLinearMap; -- toCLE?
     have hv': ‖Q‖ ≤1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; change ‖LeadK.repr i j‖≤ _; rw [←LeadK.repr.norm_map i]; exact PiLp.norm_apply_le _ _ -- lemma
     have hg:Allows p.order (K ∘ M) 0 (v/(x*t')):=by
         apply Allows.mono ((Allows.linear Q (milk_H o h U w) hv').smul (1/(x*t'))); apply le_of_eq; rw [abs_of_pos (by positivity:0 < 1/(x*t'))]; ring
     have hT:Allows p.order (T ∘ M) 0 R:=by
         have hp:= (k t' e p.threshold_le o U w).1; have hg:Push.Uniform.Allows p.order (T∘ M) 0 R:=Push.Uniform.Allows.germ ((packs (fog GS (More n)) (Turret o p.threshold ∘ βten t' U) hp (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=> by change ‖((v,0):tandem GS (More n))‖≤_; simp))).order (Nat.le_trans s (by decide:6≤7))) (Eventually.of_forall (fun i=>?_)) -- tune goal
         · exact ⟨hg.analytic.of_le le_top,hg.norm_le⟩
         change L (increment (increment U (p.threshold • i)) _)= _; simp [M,T,L,t',Shield.solo]
     refine Allows.mono ((((Allows.bilinear (ContinuousLinearMap.mul ℝ ℝ) hg hT le_rfl).smul (-1)).germ (Eventually.of_forall (fun i=>?_)))) ?_
     · change (-1:ℝ) • ((K ∘ M) i*(T ∘ M) i)= - (_*_); rw [neg_smul,one_smul]; rfl
     let V':=‖ContinuousLinearMap.mul ℝ ℝ‖; rw [abs_neg, abs_one, one_mul]; change 2^p.order*V'*(v/(x*t'))*R≤_; have hz:(0:ℝ)≤ v:=zero_le_one.trans hv; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ)^p.order≤b from pow_le_pow_right₀ (by norm_num) s) (by unfold V'; positivity)) (by positivity)) hU); apply le_of_eq; unfold D V'; ring
 refine ⟨(J _ (ping_f p _)).nonneg, ?_,?_,J⟩
 · have hp:Continuous (GDecr o p l f x j):=((contour_val o l f p x j).mul (continuous_iff_continuousAt.mpr fun i=> lively i (turret_π o p.threshold i).continuousAt)).neg; exact Env.compact hp
 intro U V p'; unfold GDecr dimeT Lamp; rw [h.live _ _ p', turret_sees o _ U V p']
end MastTin
end YM.CF.XGarden
end
