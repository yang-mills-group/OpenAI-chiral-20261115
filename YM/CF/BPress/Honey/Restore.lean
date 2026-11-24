import YM.CF.BPress.Sugar.Vortex
import YM.CF.BPress.Honey.Wheat
/-!
 $marked physical numerator per band. Ω offsets etc. Escaped with product weight. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Honey
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Recipe Crew
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Crew A}{T:GramM (mid m s)}{X:Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u:ℝ}
variable (V: Recipe (A:=A) T) (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)
variable {p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
variable {P:Edition Y}
abbrev formula (R:Recipe (A:=A) T) (H:Crew A) (A0:A.Index→ Theatre Λ):= white A A0 R.M T.path T.funds T.p T.beta
abbrev design (sV:Calyx P (ΓStage F Q)):= candid A H.Z H.tile sV X.W.M
section price
variable (ε P)
def stall(x:H.castP): ℂ:= Real.exp (Wage H V x.val) • Report F Q ε P x
-- density exactly. With pointwise versions Pose terms, not imposing all support conditions outside.
def Price(x:mState Λ A):ℂ:= if v:H.Role x then stall ε V F Q P ⟨x,v⟩ else 0 -- tune P implicit binder
end price
variable {V F Q}
variable (K:Budgeting H V τ u D ζ δ C)(sV:Calyx P (ΓStage F Q))(L:Passports Y T G h P p3 q d ε t v) (g:0≤t)(γ:0<ε) (f:List A.Index) (b:Orbit (mid m s) → Phys (mid m s))
abbrev song: A.Index→ Theatre Λ:= formula V H (design F Q sV) -- ORE
abbrev cashmark (V: Recipe (A:=A) T) (u:ℝ) (p3:Pledge) (v:ℝ) (i:A.Index) := costW A T.funds T.beta V.C u (K:=fun i=> Silhouette.heightP (W:=p3) A i v) i
include K L g
lemma marks (i : A.Index): YM.CF.BPress.Extends H.Z A i ((song (V:=V) sV) i) (cashmark V u p3 v i):= whiteMark A H.Z _ (fun i=> candid_p A H.Z H.tile sV X.W.M i L g) V.M T.path T.funds T.p T.beta V.work K.money i -- tune arguments
include γ
lemma harborEnv : Envelope (stall ε V F Q P):= Env.scale K.fair (reportEnv L γ.le)
lemma Price_E : Envelope (Price ε V F Q P):=by
 let S:={x|H.Role x}; have ht:=harborEnv (F:=F) (Q:=Q) K L g γ; obtain ⟨i,z⟩:=ht.cost; refine ⟨Measurable.dite (s:=S) ht.meas measurable_const (H.Role_meas),max 0 i,fun x=>?_⟩; unfold Price; split; exact (z _).trans (le_max_right ..); rw [norm_zero]; exact le_max_left .. -- tune
omit K L g γ
/-- obtained pointwise from §Spin (`Sugar.Crew.event`). Here b = offset-removed density in use. -/
structure Pin :Prop where
 env:Envelope b
 s:f.Nodup
 D:∀ t,t∈f
 event(x:H.castP): encore (T:=H.T) (y:=H.y) A f (design F Q sV) (relieve b T.path T.funds T.p T.beta) (layout x.val) (H.harborT x.val)=∫ z: Rod Λ,(∫ v,Report F Q ε P (κS x z v)∂ Wheel.coin (Site Λ))∂ Wheel.coin (Site η)
namespace Pin
variable (k':Pin sV f b (T:=T) (ε:=ε))
include K L g γ k'
abbrev 𝒟(w:A.Slates):= encore (T:=H.T) (y:=H.y) A f (formula V H (design F Q sV)) b w
lemma point_s (x:H.castP):
 jstamp (y:=H.y) A H.J H.F x.val.1 x.val.2.1 • 𝒟 (V:=V) sV f b (layout x.val) (H.harborT x.val)= Credit H V • ∫ z:Rod Λ, (∫ v, stall ε V F Q P (κS x z v)∂ Wheel.coin (Site Λ))∂ Wheel.coin (Site η):=by
 let v':=Real.exp (directW H V x.val); let T':=Real.exp (Wage H V x.val); let c:=Credit H V; let x':=H.harborT x.val; have he : 𝒟 (V:=V) sV f b (layout x.val) x'=v' • encore (T:=H.T) (y:=H.y) A f (design F Q sV) (relieve b T.path T.funds T.p T.beta) (layout x.val) x':=by rw [Complex.real_smul]; exact white_eq A f (design F Q sV) b V.M T.path T.funds T.p T.beta V.work _ _ K.money x' (K.pay _) (layout x.val) k'.s k'.D
 change _ • 𝒟 (V:=V) sV f b (layout x.val) x'= _; rw [he,smul_smul, show jstamp _ _ _ _ _*v'= c*T' from K.vault x, k'.event]; apply Eq.trans (mul_smul ..); congr 1; unfold stall; simp_rw [show ∀ i z, Real.exp (Wage H V (κS x i z).val)= T' from fun _ _=>rfl, integral_smul] -- tune syntax.
lemma apply_s : House.Theater A H.κ H.J H.F (𝒟 (V:=V) sV f b) (fun x=> Credit H V • Price ε V F Q P x) H.Z:=by
 refine ⟨fun w=> encore_env A H.Z f _ (marks K sV L g) b k'.env w, Env.scale (f:=Price ε V F Q P) (Envelope.const _) (Price_E K L g γ),fun i W U t z m=>?_⟩
 let x:mState Λ A:= (i,W,U,t,1,1); split; next h=>
    let v:H.castP:=⟨x,⟨⟨z,m⟩,h⟩⟩; change _= jstamp (y:=H.y) A H.J H.F _ _ • 𝒟 (V:=V) sV f b (layout v.val) (H.harborT v.val); rw [point_s K sV L g γ f b k' v]; have hu (z:Rod Λ)(w:ActY Λ): Price ε V F Q P (i,W,U,t,z,w)=stall ε V F Q P (κS v z w):= dif_pos (castB v z w); simp_rw [hu, integral_smul]
 next h=>
    have he (z:Rod Λ)(v:ActY Λ) : Price ε V F Q P (i,W,U,t,z,v)=0:= dif_neg (fun p=> h p.2); simp_rw [he]; simp
lemma reflect_s (x:Fast H.y)(h:0<paysP (B:=B) R H.y): Net.lantern A H.Z f (formula V H (design F Q sV)) b=
 (Credit H V * wool A R H.y) • ∑ E, ∫ v,Price ε V F Q P (House.read A R v) ∂ Century A R H.y E :=by
 have he:= House.Theater.threshold (apply_s K sV L g γ f b k') K.afford K.jRoot K.summer (fun S=>(K.poly S).lid) x R h; refine he.trans ?_; simp_rw [integral_smul]; rw [← Finset.smul_sum, smul_smul, mul_comm]
end Pin
end YM.CF.BPress.Honey
#print axioms YM.CF.BPress.Honey.Pin.reflect_s
#print axioms YM.CF.BPress.Sugar.Crew.event
