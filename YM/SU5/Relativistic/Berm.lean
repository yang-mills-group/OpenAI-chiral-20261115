import YM.SU5.Relativistic.Featsby
import YM.SU5.Relativistic.Hopscotch
/-! # Purchases, keeping track of M horizon; checking real estimate on the chosen course. Includes raw power bill. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.ScreeV
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner

private lemma tender_g(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
open Satin Tapestry
open CF.Crest CF.Crest.Sleet
open _root_.YM.CF.Buffered.Afterglow.Tower.SlabMark
-- sermon before s so κ fixed. angles clocks config. want Column for each γ. move Stage using terrain.
private lemma switch_tw {K:Calibration}{z m:Side}(v:K.c z=m)(ν:Mark m→ℂ)(j:ℕ)(R:ℝ)(d:ℕ)(M:Tulip.Male)(p:StageTw K ν j R d M): StageTw K (ν ∘ arrange _ _ v) j R d M:=by subst m; exact p
lemma tufts {γ γ' κ ε R R' δ:ℝ}{A C E η T:ℝ}{q d w z u B:ℕ}
    (hv:FairRoute P.P P.J P.h P.N0 Chi.canonical)(h: WealthF T)(h₀:0≤T)(W:∃ N:ℕ,∀ ξ> (0:ℝ),∃ γ> (0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter P.K.j δ n γ w ξ)(hη:0<η)(tη:η≤1)
    (p: Inflation A P)(e:0<E)(v:E≤1)(hp:(η^2)⁻¹*E⁻¹≤P.h)(g:P.d ≤δ)
    (c:∀ᶠ n:ℕ in atTop,∀ (N:Side),n≤ N.val → Winter P.K.j δ N γ w κ ∧ Winter P.K.j δ N γ' u ε ∧ ∀ M:Tulip.Male,∀ b S,Sparse d S → HearthB R (sp b P.K.j M (1:Pane N)) S)
    (hvK:0<R')(t: κ*R≤1/3)(v': (ε*R'+C)+2*R*(ε*R'+C)≤E^3)(d0:5*(E*(R'+4)*meridiem R')≤Real.exp (-2*(5+meridiem R'-12*Real.log (η^2))))
    (f:T*η+η ≤ heels P.block (addgap (tent Y H)) q B)(zt:P.J.n+u≤z)
    (X:Buffered.Family (tent Y H))(S:Finset Cover)(hB:InTest (tent Y H) true S false X)(B0:Tower.SlabMark.Between (tent Y H) TA 0 (ruler P.block*(heightB B)) S)(x₀:Cover)(hX:Transom TA S x₀ (q))
    (cost:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ᶠ k:ℕ in atTop, CF.Pannier.Chancel.ScreeV.Batch (tent Y H) X S 1 (momentm Y i s) P.K.j (gram Y s i k).J.M 1 w d u z γ γ' ((gram Y s i k).p.threshold) C R'):
     ∀ᶠ s in atTop,∀ n:ℕ,∀ᶠ i in atTop,∀ᶠ k in atTop, ‖sharp Y H s i k (thicket (tent Y H) TA (heightB B) X n)‖ ≤ Real.exp (-2*staveP n):=by
 let G:= (5+meridiem R'-12*Real.log (η^2))*(4*(z+z+1)^4*1:ℕ); let K:=tent Y H; let F:=P.block; have hx:Tendsto (fun s:ℕ=>temp (hat P.R.L P.x s)) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 have hk:0 < (1:ℕ):=by decide
 obtain ⟨w₀,l⟩:=c.exists; obtain ⟨w',vM⟩:= flatAcross P.K.j (P.kJ ▸ (by decide)); let B₁:=heightB B; have hq:0<B₁:=by unfold B₁ heightB; positivity
 filter_upwards [lease_h Y hv (show 0≤(η^2)⁻¹*E⁻¹ by positivity) hp p g W h h₀ hη tη η G hη (by
    unfold G; have ht:0≤ meridiem R':=by unfold meridiem; positivity
    have hρ:Real.log (η^2) ≤ 0:=Real.log_nonpos (by positivity) (pow_le_one₀ hη.le tη); exact mul_nonneg (by linarith) (by positivity)),cost,hx.eventually (ge_mem_nhds P.J.ht)] with s YQ bF hr n -- p
 let p':=thicket K TA B₁ X n; obtain ⟨S',u',Bh,Xg,H',Sl⟩:= Thicket.express (z:=TA) hq B0 x₀ hX hB n -- named arg `z`
 let T':= singleTick K B*staveP n; let D:=(T'+q+addgap K) + w₀+w'+u';
 filter_upwards [bF,YQ,(count_grows Y s).eventually_ge_atTop D] with i hz Bt S0
 let N:=Papal.count Y s i; let m:=momentm Y i s; let Ω:= (More N).val
 have hk₀:K.c m=N:=terrain ..; have ht':D ≤ N.val:=S0; obtain ⟨x1,x2,x3⟩:= l N (by omega)
 let eK:= Real.exp (-4*sites N); let A0:= 1+meridiem R'; have hP:0≤ meridiem R':=by unfold meridiem; positivity
 let V':= A0^(Ω^4*1); have hx:0<V':=by unfold V' A0; positivity
 filter_upwards [hz,ferry_later Y s i,thaw_plot Y (eK/V') (by unfold eK; positivity) s] with k S hp consi
 let WP:= (gram Y s i k); let b:=WP.p.threshold; have hQ: b = temp (hat P.R.L P.x s) := (congrArg BudgetPoint.threshold (prices_plot Y s i k hp.enters).1).trans (Y.meter.boot s).1
 let Y₁:= compass Y i k s; let Z:=solder Y i k hp.depth s; let M:=WP.J.M
 have kP:StageTw K Z P.K.j R d M:= ⟨tender_g Y H s i k hp,vM N (by omega) _,x3 _⟩
 have hG₁:CF.Pannier.Chancel.ScreeV.Batch K p' S' (staveP n) m P.K.j M 1 w d u z γ γ' b C R' := Sl m (by rw [hk₀]; omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (switch_tw hk₀ Z _ _ _ _ kP) S
 rw [actualRead]; change ‖Y₁ (arrange _ _ hk₀ (p' m))‖ ≤ _
 apply cornice (m:=N) Y₁ Z M TA hk₀.symm kP hvK.le B (by change T'+_ ≤ N.val; unfold D at ht'; omega) (by change _ ≤ N.val; unfold D at ht'; omega) _ _ S' p' Bh x₀ Xg hG₁
 · intro L Lx hx0; have hs: ‖Y₁ (CF.Pannier.Chancel.Cliplet.probe L)‖ ≤ _ := Bt k hp.depth hp.enters _ (-(5*(L.length*1:ℕ))) Lx.corsage.env (fun x=>?_) -- allocate Yep
   apply hs.trans; apply Real.exp_le_exp_of_le; rw [mul_one L.length]; have he:(T*η+η)*sites (Papal.count Y s i) ≤ (L.length:ℝ):= (mul_le_mul_of_nonneg_right f (show 0 ≤ sites N by unfold sites; positivity)).trans hx0; linarith only [he]
   have hY(k):Sea (Fock.cutM (Tset (Papal.count Y k i))) (mateK _):= by rw [←touchP]; exact tickB ..
   rw [touchP]
   exact iced Lx hvK _ _ (roofage Y i s) (show b≤ P.J.k from hQ ▸ hr) zt (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _) (P.dpos.le.trans g) g x1 x2 (fun i h b=> x3 _ _ _ h) t E e v v' (η:=η^2) ⟨(by positivity),pow_le_one₀ hη.le tη⟩ 5 d0 (by norm_num) hk x _ _ (safety Y s i k x).2 (hY s)
 intro L h; exact (show ‖Y₁ (CF.Pannier.Chancel.Cliplet.probe L)- Z (CF.Pannier.Chancel.Cliplet.probe L)‖ ≤ (eK/V')*V' from consi i hp.depth _ V' h.corsage.env (fun x=> (h.bill (by positivity) x).trans (pow_le_pow_right₀ (by linarith only [hP]) (Nat.mul_le_mul_right _ (h.pcount hk))))).trans_eq (div_mul_cancel₀ _ hx.ne')
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.tufts
