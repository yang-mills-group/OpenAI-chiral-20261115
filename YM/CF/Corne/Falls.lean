import YM.Planned.PRIMARY_INTEGRAL_295.Xacts
import YM.CF.Corne.Vest
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d α:ℝ)(l:ℕ)(M: Monk G S)(J:ChartRatio G)(t β:ℝ)
local notation "a₀"=> M.key
local notation "M₀"=> bunk S P 1
lemma stillW(h:K.Funds S T): (bunk S P 1).fuel x T q d l β=0∧ (bunk S P 1).sent x T q d l β=1:=by
 let F:=P.1; have hp : (bunk S P 1).fuel x T q d l β=0:=by -- quotation ?
    rw [oasisN T q x d l (M:=M₀) rfl]; funext i; unfold liftN; split; exact congrFun (shyX (x:=x) Thera.yet_one h F P.2 q d l) i; next z=> exact False.elim (z (by unfold green; simp [bunk,bareStores,Stores.dome,Stores.place,halo_spec]))
 refine ⟨hp,?_⟩; change landed _ _ _ _ _ ((bunk S P 1).fuel x T q d l β)=_; rw [hp]; have he:= Slate.landed_exit (F:=P.1) (x:=x) (1: Config G c) (0:Fish (Key P.1 G)); rw [map_zero,map_zero,Work.G07.at_zero_increment,replica_one] at he; exact he -- tune
lemma yen {c:Side}(V:Cell c): faceValue (1:Config G c) V=1:=by rw [← (link_one («G»:= SU.group))]; apply Push.stroll_zero
lemma gnull(X:ℕ→ RG.Atom G 2)(c:Side)(i:Site c): gplot X (1:Config G c) i=0:=by
 have hx(A: RG.Atom G 2): A.unmasked (1:Config G c) i=0:=by unfold RG.Atom.unmasked RG.Atom.poly; simp [Work.F03.atSite_path,yen]
 unfold gplot; simp_rw [hx]; simp
lemma glowI(h:K.Funds S T)(i:Site c): ink T x q d α l β i M₀=0 := by
 unfold ink; have hv(k:Signed)(j:Along S): fle T x q d α l β k j M₀=0:=by
    unfold fle; rw [show (bunk S P 1).V=1 from rfl,(stillW T x P q d l β h).2,coldPull (1:Config G c),coldPull (1:Config G f)]
    rcases j with (i | i | i|i)|i|i; exact rfl; exact rfl; dsimp only [TaleX]; rw [Slate.manta,yen]; simp [Planned.PrimaryIntegral295.Xacts.plotted_zero, sore]; exact rfl; exact gnull _ _ _; dsimp only [TaleX]; rw [gnull,neg_zero]
 unfold averaged; simp [hv]
lemma curve_l(h:K.Funds S T)(hX:LocalRatio J) (i:Site c): flat_w T x q d α l M β J t i=0:=by
 let K: Tab S:= (M.park,M.k); unfold flat_w kist; rw [glowI T x K q d α l β h]; unfold kite dua flare; rw [sub_zero]; rw [(stillW T x K q d l β h).1]; have he:(tape (0 : Prices G (Active _ _ _)))=(0:LogArray G (Active (bareStores S) x K.1)):=Next.SectorChange.colors.map_zero; rw [he]; simp [logGuard,hX.anchored]
-- Need certificate from actual tag & volume. Add orientation TaurusW purchase
lemma wants (u:ℝ)(h:0<u)(n j:ℕ)(p:1 ≤ n) : ∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(M:Monk G S), M.key.flags=RG.flags (temp x) M.V→ (j+j+101)*radiusB x ≤ c.val → ∀ k:Site c,k∉ M.key.dome ((j+2)*radiusB x)→ Taurus u M ((j+1)*radiusB x) k :=by
 obtain ⟨A,hA,H⟩:=hustle G j n p; filter_upwards [H,(tide_s A).eventually (ge_mem_nhds h)] with x H hx c f S M hp p i hu; obtain ⟨V,b,t,v⟩:= H.2.2 _ _ _ _ hu hp p; let Y:=satU G (tideF A x) (V 0)
 have he:tideF A x ≤ u:= hx; let r:=tideF A x/u; have ht:0≤r:= (div_pos H.1 h).le; have hr:r≤1 := (div_le_one h).mpr hx; have hv:satU G u (r • (V 0))=Y :=by unfold satU Y satU; rw [←mul_smul,show u*r=tideF A x from mul_div_cancel₀ _ h.ne'] -- tune
 have hZ:Tarn.drift G i ((j+1)*radiusB x) (Lattice.gauge b M.V) Y:=by have he:= v.self_of_nhds; simp only [Vmove,smul_zero, Work.G07.at_zero_increment] at he; exact fun i t=>he i t
 constructor; refine ⟨b⁻¹,Y,hv ▸ pine_p _ _ ?_,?_⟩; rw [norm_smul_of_nonneg ht]; exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans_lt (t.2.value.trans_lt (by norm_num)); have he:=hZ.face.via b⁻¹; rwa [Tarn.dyadic,inv_mul_cancel,fix_s] at he
end YM.CF.Corne
