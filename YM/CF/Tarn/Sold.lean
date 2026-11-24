import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Base
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
-- post-L
variable {T:Tube G S}{K:Teller G}{s y:ℝ}
open Stationary Push.Loops Hors
open RG Precision Pressure
-- Pure thermal single ratio & alpha. perturb after L total. RHS nib Λ.
theorem lampZ(K:Pressure.Teller G)(P:Patch)(n l:ℕ)(p:P.Branches K.bind G)(hn:3 ≤ n)(hk:1 ≤ l)(hl:l≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2))(X:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(Z:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind 5)(q:Chi)(J:ChartRatio G)(hj:LocalRatio J)(r Λ Θ v B:ℝ)(hr:0<r)(hZ:4*r<J.radius)(hθ:0≤ Θ)(hv:0<v)(hB:0 ≤ B):∃ u M f b m,0<u ∧u ≤ 1∧ CapY M ∧ nib f ∧ nib b ∧ 0 < m ∧∀ᶠ x:ℝ in atTop,∀ {c f':Side}(S:StepData (More c) f')(T:Pressure.Tube G S), Cert P K S T x→ T.up.Bounds T.high K.top.width K.top.paths Λ → T.down.Bounds T.low K.below.width K.below.paths Λ →∀(α:ℝ),|α| ≤ B → (∀ k:Tab S,sizedP G P K S T k.1)→ (∀ k:Tab S,∀ z,Critical k.1 T.high T.up z→ FiniteBound k.1 T.up T.down T.high T.low α J z Θ v 1) → let R:=radiusB x; R ≤ (More c).val→ M R< (More c).val→
 (∀ k:Tab S, FreshT T x u q J r α Λ n l k (f R) m) ∧ forall d:ℝ, let Q:= Coin T x u q J r d α l; ∃ D,Wick Q D (M R) n u (f R) (b R*temp x):=by
 obtain ⟨u,V,m,hu,ht,hV,hm,H⟩:= sant K P n l p hn hl W X q J hj r Λ B hr hZ hB
 obtain ⟨A,C,D,hA,hC,hD,H'⟩:= Souk.hercule K P p l hk hl Z Thera.yet_one J hj Θ v Λ
 let e:= (LinearIsometryEquiv.refl ℝ SU.group.Color).toLinearIsometry; obtain ⟨M,f,hM,hvM,hf,Hm⟩:= tuft n (by omega) e
 let N(i:ℕ):=(l+76)*i; let M':= M∘N; let E(i:ℕ):=A*(raised G P.L ((l+52)*i)+1)*(i:ℝ)^27+2; let V'(i):= V i+ E i; let b(i):= E i*f (N i); let F(i):= V' i*(1+ f (N i)); have hN:CapY N:= CapY.lives.scal _; have hb':nib (fun i:ℕ=>(i:ℝ)):=by -- tune
    exact nib.mate CapY.lives
 have hE:nib E:= (((nib_const _ hA.le).mul ((nib_raise _ _ _).add (nib_const _ zero_le_one))).mul (hb'.pow 27)).add (nib_const _ (by norm_num))
 have hV':nib V':= hV.add hE
 refine ⟨u,M',F,b,m,hu,ht,CapZ hM hN,hV'.mul ((nib_const _ zero_le_one).add (TargetV hf hN)),hE.mul (TargetV hf hN),hm,?_⟩
 filter_upwards [H,H',courtT P.L K.below.width (C*B+D) K.below.width_pos (by positivity),crystal v Θ hv hθ,(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds zero_lt_one), Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, PatchReads.reserve K P] with x h h' hT hZ' h₀ hR hv' c f' S T hK hU hW α ha hS hc R hL hQ
 have hT'(k:Tab S):=h S T hK hU hW k (hS k) α ha
 let L:= N R; have he:0≤ V' R:=hib hV' _; have hx: V R ≤ V' R:= le_add_of_nonneg_right (hib hE R); have hφ : f (N R) ≤ 1+f (N R):=le_add_of_nonneg_left zero_le_one; have hz: V' R ≤ F R:=le_mul_of_one_le_right he (le_add_of_nonneg_right (hib hf _)) -- tune
 constructor
 · intro k; exact ⟨fun d i=>⟨((hT' k).bonds d i).1.under le_rfl le_rfl (hx.trans hz), ((hT' k).bonds d i).2⟩,(hT' k).growth,(hT' k).pureT⟩
 intro d Q'; let U: FileM _ G:= fun i=> Arena.aria (fun t=> Q' t i)
 have hP(k:Tab S): Prox (Q' k) 2 (E R*temp x):=by
    apply proxS _ _ _ _ _ _ _ _ _ _ _ (hT' k) (by omega) hu
    intro i g; obtain ⟨hv,h⟩:= h' S T k.1 hK (hS k) hU hW α (hc k) k.2 q d i; refine ⟨hv.of_le (by norm_num),h.trans ?_⟩; rw [hK.got]; refine le_trans (add_le_add (add_le_add le_rfl (hZ' (L:=More c) hL)) ((mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left ha hC) le_rfl) (show 0≤ tollE _ _ from (Real.exp_pos _).le)).trans hT)) (le_of_eq ?_); unfold E; unfold R; ring
 let H(V:Tab S):= (hT' V).growth; have hr': Ready T x:= hv' _ _ hK.got hK.size hK.funds.1; have hs:0 ≤ E R:=hib hE _
 obtain ⟨A,hA⟩:= Hm S L Q' u (V' R) (E R*temp x) hu ht (mul_nonneg hs (temp_nonneg x)) ((mul_le_of_le_one_right hs h₀).trans (le_add_of_nonneg_left (hib hV _))) hQ (fun z v i h=>scopeR T x u z q J r d α l i h hr' hR) (fun t i=> ⟨((hT' t).bonds d i).1.under le_rfl le_rfl hx, ((hT' t).bonds d i).2⟩) hP (fun i j=> salt T x u q J r d α l hK.funds.1 hr' hR hm H hj hZ hr _ _) (selfD T x u q J r d α l 0 hK.funds.1 hr' hR hm H hj hZ hr hu)
 exact ⟨A,hA.axis,fun t i j=>(hA.vows t i j).under (mul_le_mul_of_nonneg_left hφ he) le_rfl le_rfl,hA.patch,fun t i=> (hA.better t i).under (mul_le_mul_of_nonneg_left hφ he) (le_of_eq (by unfold b L; ring)) le_rfl⟩
end YM.CF.Tarn

#print axioms YM.CF.Tarn.lampZ
