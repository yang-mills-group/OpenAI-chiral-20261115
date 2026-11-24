import GaugeFieldConstruction.Bask
import GaugeFieldConstruction.Pipeweed
import YM.CF.Girt.East
/- commuting gauge cost with zero identity. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B n:Side}{j:ℕ}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive
local notation "GS"=>SU.group
local notation "Λ"=> CSide m B
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable (g:Agora n)(F:Paper n){P:BudgetPoint}{c h v a d:ℝ}{o:Seat n}
abbrev CivilPack(Y:Torches n):Torches n:=(civilM Y.1, fun X=>civilM (Y.2 X))
abbrev TiltForm(g:Agora n)(Y:Torches n):Torches n:=(censusF g Y.1, fun X=>censusF g (Y.2 X))
lemma civic_root : civilM (0: Paper n)=0:=by
 funext i x; unfold civilM censusF CardCraft; simp_rw [stripeQ,αLines,Pi.zero_apply,Ione.sign0,mul_zero,sum_const_zero,integral_zero]
lemma citizen_X (Y:Torches n)(p: Inscribe P o h a Y c d): Inscribe P o h a (CivilPack Y) (CaseL*c) (CaseL*d):=by
 refine ⟨civil_H Y.1 P h c p.1,?_⟩; obtain ⟨V,Q,z⟩:=p.2; refine ⟨fun i=>CaseL * V i, fun i=> ⟨civil_H _ _ _ _ (Q i).1,fun p=>?_⟩, ?_⟩
 · change civilM _=_; rw [(Q i).2 p, civic_root]
 simp_rw [mul_left_comm (rent _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left z (by positivity)
def LegTax(Y:Torches n):Prop:=portable Y.1∧∀ i,portable (Y.2 i)
lemma citizen_T(Y:Torches n)(p: Inscribe P o h a Y c d): LegTax (CivilPack Y):= ⟨civil_V _ _ _ _ p.1,fun i=>by obtain ⟨V,Q,z⟩:=p.2; exact civil_V _ _ _ _ (Q i).1⟩
lemma optics_T (Y: Torches n) (x:Pane n):Ion Y x=marketD Y.1 x+∑ i,marketD (Y.2 i) x:=by unfold Ion; rw [conn_X,Pi.add_apply,Finset.sum_apply]
lemma monk_T (g:Agora n) (F: Paper n) (x:Pane n) : Gaze g (marketD F x)=marketD (censusF g F) (GA g x):=by have he:=exportD (tradew n g) false false (αLines F x); rw [←censusK F g x] at he; exact he
lemma orient_T (g:Agora n)(Y: Torches n) (x: Pane n): Gaze g (Ion Y x)=Ion (TiltForm g Y) (GA g x):=by rw [optics_T,optics_T,map_add,map_sum]; simp_rw [monk_T]
lemma cashM_T{S:Hubber n}(F: Paper n)(p:TrackD P S h F c): Envelope (fun v:Agora n × Pane n=> marketD (censusF v.1 F) v.2):=by
 refine Env.total _ (fun j:Wa n=> ?_); exact Girt.pole_w (fun v:Agora n × Pane n=> censusF v.1 F j v.2) (· • dot_Q j) (continuous_id.smul continuous_const) (volumeDeck F P h c p j) -- tune
lemma cashM_r{S:Hubber n}(F:Paper n)(p:TrackD P S h F c)(x:Pane n): marketD (civilM F) x=∫ v:Agora n,marketD (censusF v F) x∂HaarG n:=by
 unfold marketD; rw [integral_finsetSum];
 · apply sum_congr rfl; intro i _; let H(v:Agora n):= censusF v F i x; change (∫ v,H v∂HaarG n) • _= _; exact (integral_smul_const ..).symm -- ℂ smul integral
 intro i _; refine Integrable.smul_const ?_ _; exact Env.integrableX (Env.along (volumeDeck F P h c p i) (g:=fun k:Agora n=> (k,x)) (measurable_id.prodMk measurable_const)) _
lemma Ion_r (Y:Torches n)(p:Inscribe P o h a Y c d)(x:Pane n): Ion (CivilPack Y) x=∫ v:Agora n,Ion (TiltForm v Y) x∂ HaarG n:=by
 obtain ⟨p, U,Q,u⟩:=p; let μ:=HaarG n; let I(i:Hubber n)(v:Agora n):= marketD (censusF v (Y.2 i)) x; have he(i):Integrable (I i) μ:=Env.integrableX (Env.along (g:=fun v:Agora n=> (v,x)) (cashM_T _ (Q i).1) (measurable_id.prodMk measurable_const)) _
 simp_rw [optics_T]; rw [integral_add (Env.integrableX (Env.along (g:=fun v:Agora n=> (v,x)) (cashM_T _ p) (measurable_id.prodMk measurable_const)) _) (integrable_finsetSum _ fun i _=> he i),integral_finsetSum univ (fun i _=> he i)] -- tune expression elaboration
 apply congrArg₂ (· + ·) (cashM_r _ p x); exact sum_congr rfl fun i _=> cashM_r _ (Q i).1 x
lemma Ion_pay (Y: Torches n)(p: Inscribe P o h a Y c d) : Envelope (fun i:Agora n×Pane n=> Ion (TiltForm i.1 Y) i.2) :=by
 obtain ⟨p,V,Q,k⟩:=p
 simp_rw [optics_T]; let K:= Y.1; let F(i:Agora n×Pane n):=marketD (censusF i.1 K) i.2; let D(l)(i:Agora n× Pane n):=marketD (censusF i.1 (Y.2 l)) i.2
 change Envelope (fun i=> F i + ∑ v,D v i); exact Girt.kitE F _ (· + ·) (continuous_fst.add continuous_snd) (cashM_T _ p) (Env.total _ fun i=> cashM_T _ (Q i).1)
lemma currency_Y{R:Paper n}(p:TrackD P (Pach o) h R c): Envelope (marketD R):= val_T p
lemma ga_C : Continuous (GA g):=by unfold GA Lattice.gauge; apply continuous_pi; intro i; fun_prop
lemma ga_embed : MeasurableEmbedding (GA g):=by
 let h: Pane n≃ₜPane n:=⟨⟨GA g,GA g⁻¹,fun x=>by nth_rw 2 [←inv_inv g]; rw [goZ], fun x=>goZ ..⟩,ga_C ..,ga_C ..⟩; exact h.measurableEmbedding
lemma gov_p : MeasurePreserving (GA g) (prior GS (More n)) (prior GS (More n)):=by
 apply measurePreserving_pi (α:=fun _ : Bond (More n)=>SU.group.El) _ _ (f:=fun i u=>g i.1 *u*(g (i.1+ Lattice.step i.2))⁻¹); intro i; exact (measurePreserving_mul_right SU.group.probHaar _).comp (measurePreserving_mul_left SU.group.probHaar _)
section act
open Dial
abbrev BookP (F:marker0 n)(i:Pane n)(Y:trans1 n): FC (Single n)→L[ℂ] ℂ:= (⟨⟨fun V=>letterRead (F i*V) (Y i),fun A B=>by rw [mul_add]; unfold letterRead; change inner ℂ (mateK n) (acts (F i*A+ F i*B) (Y i))=_; rw [act_add,inner_add_right]; rfl⟩, fun a V=> by change letterRead (F i * (a • V)) (Y i)=a • _; rw [Matrix.mul_smul]; unfold letterRead; change inner ℂ (mateK n) (acts (a • (F i*V)) (Y i))=_; rw [act_smul,inner_smul_right]; rfl⟩: FC (Single n)→ₗ[ℂ]ℂ).toContinuousLinearMap -- tune
lemma prizeH (X:Torches n)(p: Inscribe P o h a X c d)(F:marker0 n)(u:Envelope F)(Y: trans1 n)(q:Envelope Y) : UnEcho (Ion (CivilPack X)) F Y= ∫ g:Agora n, UnEcho (Ion (TiltForm g X)) F Y ∂ HaarG n:=by
 let f(x:Agora n×Pane n):=BookP F x.2 Y (Ion (TiltForm x.1 X) x.2)
 have hp: Integrable f ((HaarG n).prod (prior GS (More n))):= Env.integrableX (env_letterRead (env_mult (Env.along (g:=Prod.snd) u measurable_snd) (Ion_pay X p)) (Env.along (g:=Prod.snd) q measurable_snd)) _
 change (∫ x,BookP F x Y (Ion (CivilPack X) x)∂ prior GS (More n))=∫ g:Agora n,(∫ i:Pane n,f (g,i)∂prior GS (More n))∂ HaarG n; rw [← integral_prod f hp,integral_prod_symm f hp]; apply integral_congr_ae; filter_upwards with x; rw [Ion_r X p]; exact (ContinuousLinearMap.integral_comp_comm _ (Env.integrableX (Env.along (Ion_pay X p) (g:=fun i:Agora n=> (i,x)) (measurable_id.prodMk measurable_const)) _)).symm
variable (o:Seat (CSide m B))(x:Agora (CSide m B))(X:marker0 (CSide m B))(e:Axis)
private lemma gaze_c(T:Agora n):Continuous (Gaze T):=breeze _
lemma untax_gau (p:untax (m:=m) (B:=B) o e X): untax o e (fun i=> twist (quantU (tradew (CSide m B) x))⁻¹ (X (GA x i)) : marker0 (CSide m B)):=by
 let W:= twist (quantU (tradew (CSide m B) x))⁻¹; exact ⟨Girt.pole_w (X ∘ GA x) W (breeze _) (Env.along p.1 (ga_C x).measurable),fun i j h=>congrArg W (p.2 _ _ (fun l g=> congrArg (fun v=> _*v*_) (h l g)))⟩ -- syntax
lemma gauge_mone (T:trans1 n)(p:∀ g:Agora n,∀ x,T (GA g x)= effectK (tradew n g).val (T x))(J:Torches n)(X:marker0 n)(g:Agora n) : UnEcho (Ion (TiltForm g J)) X T = UnEcho (Ion J) (fun i:Pane n=> twist (quantU (tradew n g))⁻¹ (X (GA g i))) T:=by
 unfold UnEcho; rw [← (gov_p g).integral_comp (ga_embed g) (fun x:Pane n=> _)]; apply integral_congr_ae; filter_upwards with u
 let V:=quantU (tradew n g); let W:=X (GA g u); let R:=Ion J u; rw [←orient_T, p]
 change inner ℂ (mateK n) (acts (W*twist V R) (acts V.val (T u)))=inner ℂ (mateK n) (acts (twist V⁻¹ W*R) _)
 have hx:V*V⁻¹=1:=mul_inv_cancel _
 rw [show W*twist V R= twist V (twist V⁻¹ W*R) from (by rw [map_mul, ←Fock.twin,hx,Fock.one_des]),←Fock.swivel]; nth_rw 1 [← (show acts V.val (mateK n)=mateK n from Girt.mastC g)]; exact act_unit_inner ..
lemma whole_p (Y:Torches (CSide m B))(p:Inscribe P o h a Y c d)(S:trans1 (CSide m B))(s:Envelope S)(v:∀ g:Agora (CSide m B),∀ x,S (GA g x)= effectK (tradew _ g).val (S x))(l:∀ F, untax (m:=m) (B:=B) o e F → UnEcho (Ion Y) F S=0)(q:untax (m:=m) (B:=B) o e X):UnEcho (Ion (CivilPack Y)) X S=0:=by rw [prizeH Y p X q.1 S s]; simp_rw [gauge_mone S v Y, show ∀ g:Agora _, UnEcho (Ion Y) (fun i=> twist (quantU (tradew (CSide m B) g))⁻¹ (X (GA g i))) S=0 from fun g=>l _ (untax_gau o g X e q),integral_zero]
end act
end MastTin
end YM.CF.XGarden
end
