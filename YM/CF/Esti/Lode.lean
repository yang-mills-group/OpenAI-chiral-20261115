import YM.CF.Esti.Tire
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
lemma wind(P:Teller G)(Q:Patch)(h:Q.Branches P.bind G)(n l:ℕ)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2)) (q:Chi)(width:ℝ)(hv:0<width)(hp:2 ≤ n)(hl:l ≤18):∃ A B:ℝ,0<A∧0<B∧∀ᶠ x:ℝ in atTop,∀ β∈Set.Icc (Scales.y G Q.L x/2) (2*y G Q.L x),
 let t:= fiery G x Q.L
 let R:= B*Scales.p G Q.L x
 0 < t ∧ 0 < β ∧ 0<R ∧ wireP G (coupling β) (width*t) (A*t) A ≤ R ∧∀ {c f:Side}(S:StepData c f)(T:Tube G S), Cert Q P S T x →∀ (Z:Stores S)(F:Forest S.ratio)(V:Config G c),sizedP G Q P S T F → Z.flags= RG.flags (temp x) V →∀ k:S.Choices, MossX n l x Z F T V k A (width*t) t q :=by
 obtain ⟨A,hA,H⟩:=turnsX n l width hv P Q h hp hl W q; let D:= Push.Uniform.shade G; have hD:=Push.Uniform.shade_pos G; let B:=D*A*(2*(2*width+A)); have hB:0<B:=by unfold B D; positivity
 refine ⟨A,B,hA,hB,?_⟩; filter_upwards [H,(year G Q.L).eventually (eventually_gt_atTop 0)] with x h ht β hβ; let g:= Scales.g G Q.L x; let p:= Scales.p G Q.L x; have hp':=Scales.pos G Q.L x
 have hh':0 < β:=(half_pos ht).trans_le hβ.1; intro t R; refine ⟨?_,hh',mul_pos hB hp',?_,?_⟩
 · rw [show t= g*p from fi ..]; exact mul_pos (Scales.gauge G Q.L ht) hp'
 · unfold wireP R; change D*(A*( (coupling β)⁻¹ * _)) ≤ _; have hx: g ≤ 2*coupling β:= (compare_v G Q.L x hβ ht).2; have hC:0<coupling β:=coupling_pos hh'; have hp:= mul_le_mul_of_nonneg_right hx hp'.le; rw [show g*Scales.p G Q.L x=t from Eq.symm (fi ..)] at hp; calc
      _ ≤ D*(A*((coupling β)⁻¹*( (2*width+A)*(2*coupling β*p)))):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hp (by positivity))) (inv_pos.mpr hC).le) hA.le) hD.le -- tune coercion
      _ = _:=by unfold B; change _ = D*A*_ *p; field_simp
 intro c f S T p A F V hp' he k; have ht:=h S T p A F V hp' he k; rw [p.got] at ht; exact ht
lemma expM(Q:Patch) {p:ℝ}(hp:0<p) : ∀ᶠ x:ℝ in atTop, fiery G x Q.L ≤ p:=by
 filter_upwards [((tally_g G Q.L 0 1).eventually (ge_mem_nhds hp))] with x h; rw [Scales.fi]; rw [pow_one,pow_zero,one_mul] at h; exact (mul_comm ..).trans_le h
structure Ticket (T:Teller G)(P:Patch)(q:Chi)(J:ChartRatio G) (n j l:ℕ)(w width γ Q x A B C D M L u m K s:ℝ):Prop where
 wear (β:ℝ)(h:β∈Set.Icc (y G P.L x/2) (2*y G P.L x)): let t:= fiery G x P.L; let Y:= B*Scales.p G P.L x; let d:=width*t; 0<t∧0<β∧0<Y∧ wireP G (coupling β) d (A*t) A ≤ Y ∧∀ {c f:Side}(S:StepData c f)(U:Tube G S), Cert P T S U x→∀(O A': Stores S)(F: Forest S.ratio)(V:Config G c)(k:S.Choices), sizedP G P T S U F → A'.flags= RG.flags (temp x) V → MossX n l x A' F U V k A d t q ∧ (Packet O A' ((j+5)*radiusB x) → PointCharge U x w γ→SafeX T P J w γ width Q j n x →∀ Y':LinkArray G (Frozen A' x F),∀ z:LogArray G (Active A' x F), ‖z‖ ≤ Y →∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E](i:E→L[ℝ] Directions G c), ‖i‖ ≤ 1→ (∀ u:E,axl A'.flags (temp x • i u)=temp x • i u) →∀ r:ℝ,(∀ y:Signed, (cardsQ (whim x j O y):ℝ) ≤ r)→ Allows n (grandP U A' O F x k q d Y' l z β J j s w (Vmove x V ∘ i)) 0 (perL S n j x w s d C D M Q γ u m L K β O A' F r))
theorem mintS(P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:2 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(S':ChartRatio G)(hp:LocalRatio S') (w width γ y':ℝ)(hw:0<w)(hy:0<width):∃ A B C D M L u m K s:ℝ,0<A ∧0<B ∧1 ≤ C ∧0 ≤ D ∧1 ≤ M ∧0 ≤ L ∧0<u∧1 ≤ m ∧0≤K∧0< s∧∀ᶠ x in atTop, Ticket P Q q S' n j l w width γ y' x A B C D M L u m K s :=by
 obtain ⟨A,B,hA,hB,H⟩:= wind P Q h n l W' q width hy (by omega) hl; obtain ⟨s,D,h',hd,hO⟩:= strut G n P Q W hn; obtain ⟨u',m,hv',hm,hr'⟩:=rene S' hp n
 let u:=min u' 1; have hu:0<u:=lt_min hv' zero_lt_one
 obtain ⟨ξ,hξ,hI⟩:=tock n; let C:=max ξ ‖(1:SU.group.Mat)‖; have hc:1 ≤ C:=hξ.trans (le_max_left ..)
 obtain ⟨b,M,hb,hM,hb'⟩:=bindsM G n s D h' hd Q
 let K:=covetM G n C M D; have hK:0 ≤ K:=by unfold K covetM Jet.composeCost dressM purM; have hh:= SU.group.colorScale_pos; positivity
 obtain ⟨G',hx,Hx⟩:= currencyT q n; let X:=purM G n*C*horse Q n C b G' K; obtain ⟨X',X''⟩:= Push.Uniform.paint_supply G n; obtain ⟨B',hp',Hs⟩:= scope_p P Q X' X C (by unfold X horse purM; have hg:= SU.group.colorScale_pos; have hd:1 ≤ max 1 (zest n * dam G n (b/2) G' C):=le_max_left ..; positivity) (le_max_right ..) n X''
 obtain ⟨a,ha,Hw⟩:= owns P Q q n width hy h
 let d:= u/(Push.Uniform.shade G*((n.factorial:ℝ)* (1+1:ℝ)^n)); let L:= a*(d+1); have hL:=Push.Uniform.shade_pos G; have ht:0<d:=by unfold d; positivity
 let C':= A+2*(2^n*A*B); have hk:0<C':=by unfold C'; positivity
 refine ⟨A,B,C,B',G',Jet.composeCost n L 1,u,m,K,b,hA,hB,hc,hp',hx,(by unfold Jet.composeCost L; positivity),hu,hm,hK,hb,?_⟩
 filter_upwards [H,Hw,order_r P Q,monitors G Q.L, (year G Q.L).eventually (eventually_gt_atTop 0), expM Q (hp:=lt_min (half_pos hb) zero_lt_one), expM Q (hp:=div_pos ht hk), Work.E01.radiusB_tendsto.eventually_ge_atTop (10*shovel Q+100)] with x hU Ht hP hy hy' hb hz hq
 constructor; intro β h t Y d0; obtain ⟨h1,h2,h3,h4,h5⟩:=hU _ h
 refine ⟨h1,h2,h3,h4,@fun c f S T e O A' F V k hO' hE=>?_⟩ -- rename
 have he:=h5 S T e A' F V hO' hE k; refine ⟨he,fun hl t₁ W Y' z p E _ _ _ i hv hJ r hg=>?_⟩
 let J:= hO S T e.got e.funds.1; have hS:= e.size; have hf: 2*(gun Q+1)< f.val:=by rw [S.sizes, e.got]; apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ Q.L.property); unfold shovel gun at *; omega
 have hX : Volo S n b D C K := by constructor; intro φ e' E _ _ U y H h; exact hb' S e.got hf _ _ J (funds_branch e.funds.1) U y C hc H h -- tune
 have hh: S.patch.L=Q.L:=congrArg RG.Patch.L e.got
 have hY: fiery G x S.patch.L ≤ min (b/2) 1:=by rw [hh]; exact hb
 refine heat (ξ:=ξ) (δ:=d) (b:=D) hn (min_le_right ..) ⟨fun v x=> hr'.cost _ (x.trans (min_le_left ..))⟩ hx (fun E _ _ f x t d b=> Hx d b) hξ (fun U N M' Xq F u θ p hV hL=> Hs S T e.got e.funds.1 _ _ _ _ _ _ _ (by unfold X; rw [←e.got]; exact u) θ p hV hL _ _ ⟨by rw [hh]; exact h1.le,hY.trans (min_le_right ..)⟩ ⟨hy.1.le,hy.2.1⟩) (fun V z h=>⟨(hI (S:=S) _ _ hy.2.1 E z h).1,(fun Y U=> (hI (S:=S) _ _ hy.2.1 E z h).2 _ _ _ U)⟩) hK hp' (zero_lt_one.trans_le ha) (le_max_left ..) _ (by rw [hh]; exact he) _ hA.le _ hX (by unfold d0 t; rw [←hh]; exact Ht S T e _ _ V hE _) e hE W hl t₁ hw hj (by rw [e.got]; omega) (hP S T e.got.symm e.funds.1) (by unfold d0 t; rw [hh]) hy.1 (by rw [hh]; exact h1) (hY.trans (min_le_left ..)) i hv hJ _ p (by rw [hh]; exact h) h2 _ hg ?_ ?_ ?_
 · rw [hh,abs_of_pos (coupling_pos h2)]; have hg:= mul_le_mul_of_nonneg_right (compare_v G Q.L x h hy').1 (show 0≤ 2^n*A*Y by positivity); apply (add_le_add_right hg _).trans; unfold Y; rw [fi] at *; refine le_trans (le_of_eq ?_) ((le_div_iff₀ hk).mp hz); unfold C'; ring
 · unfold Jet.composeCost d; exact le_of_eq (by field_simp; ring)
 unfold L; gcongr; exact hY.trans (min_le_right ..)
end YM.CF.Esti
