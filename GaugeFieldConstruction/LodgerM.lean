import GaugeFieldConstruction.Vocab
import GaugeFieldConstruction.Tripe
import GaugeFieldConstruction.Victor
import GaugeFieldConstruction.Gateveil
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
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix
abbrev Frills(o:Seat n):= platesX (Pach o) × SU.group.ColorIndex
abbrev Confab(o:Seat n):= Frills o → ℝ
def cast_P (o:Seat n): tangD n →L[ℝ]Confab o:= ContinuousLinearMap.pi fun i:Frills o => (EuclideanSpace.proj i.2).comp (toga i.1.val)
private lemma factorD (o:Seat n):∃ f:Confab o→L[ℝ]tangD n, ∀ v, cast_P o (f (cast_P o v))=cast_P o v:=by
 let X:=(cast_P o).toLinearMap; let H:=LinearMap.range X; obtain ⟨Q,h⟩:= H.exists_isCompl; let R:=H.projectionOnto Q h; obtain ⟨g,v⟩:=X.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (X.surjective_rangeRestrict)); refine ⟨(g.comp R).toContinuousLinearMap,fun v'=>?_⟩;
 let q:= X v'; change X (g (R (X.rangeRestrict v').val)) = _; rw [show R (X.rangeRestrict v').val=X.rangeRestrict v' from Submodule.projectionOnto_apply_left h _]; exact congrArg Subtype.val (LinearMap.congr_fun v (X.rangeRestrict v'))
def caster (o:Seat n): Confab o→L[ℝ] tangD n:= (factorD o).choose
lemma billΔ (o:Seat n)(W:tangD n): cast_P o (caster o (cast_P o W))=cast_P o W:= (factorD o).choose_spec W
lemma torn_K (v:tangD n)(o:Seat n)(p:300<n.val): ∃ a:Seat n→SU.group.Color, Agrees (Pach o) (v-caster o (cast_P o v)) (AnalyticBridge.VerifiedReset.gradient a):=by
 let K:= (Pach o); let x:=natural o; have he: K=knotX x 24 n:= by unfold knotX x; rw [Rush.nat_true]
 suffices hs: ∃ g:Seat n→SU.group.Color,Agrees K (v-caster o (cast_P o v)) (AnalyticBridge.VerifiedReset.gradient g) by exact hs
 rw [he]; apply TornE (by omega); intro j q; rw [map_sub]; ext i; change toga j v i-toga j (caster o (cast_P o v)) i=0; apply sub_eq_zero.mpr; exact (congrFun (billΔ o v) (show Frills o from (⟨j,by change j∈platesX K; rw [he]; exact q⟩,i))).symm
variable (p)
abbrev PressAt(f:Pane n→ℂ)(v:tangD n):ℂ:= f (increment 1 v)
abbrev ready_D (F:Paper n): Prop:=∀ i:Wa n,ContDiffAt ℝ (↑(4:ℕ)) (PressAt (F i)) 0
variable {p}
lemma readiness (W:Hubber n)(H:TrackD p W h F c): ready_D F:=by
 obtain ⟨U,Q,L⟩:=H; let G:=Shield.solo p.threshold (1:Pane n); let p': tangD n→L[ℝ]tangD n:=(p.threshold⁻¹) • ContinuousLinearMap.id ℝ _
 have hp(i:Wa n):PressAt (F i)=(F i ∘ G) ∘ p':=funext fun v=>by change F i (increment _ _) = F i (increment _ (p.threshold • (p.threshold⁻¹ • _))); rw [smul_smul,mul_inv_cancel₀ p.threshold_pos.ne',one_smul]; rfl -- tune
 intro i; rw [hp]; apply ContDiffAt.comp; rw [map_zero]; exact ((Q i).1.2.2.2 1 (Scree.ping_f p W)).smooth.of_le (Nat.cast_le.mpr (le_trans (by decide : 4 ≤6) p.order_ge)); exact p'.contDiff.contDiffAt
lemma micro_Mgrad (S:Hubber n)(L:TrackD p S h F c)(W:portable F)(s:Seat n→SU.group.Color)(v:∀ j:Wa n, F j 1=0)(u:tangD n)(g: Agrees S u (AnalyticBridge.VerifiedReset.gradient s))(i:Wa n): fderiv ℝ (PressAt (F i)) 0 u=0:=by
 let f:= PressAt (F i); let T:= AnalyticBridge.VerifiedReset.gradient s; let X:Lattice.Site (More n) → SU.group.Color:= s; let K:= FlightFlux.ChordG (G:=GS) X; let P (q:ℝ):= ((0,q):FlightFlux.Lift2 GS (More n))
 have he:fderiv ℝ f 0 u=fderiv ℝ f 0 T:=by
    have hv : (fun t:ℝ=>f (t • u))=(fun t:ℝ=>f (t • T)):=funext fun r=> (L.choose_spec.1 i).1.2.2.1 _ _ (lift_pane S r u T g) -- tune
    have he: DifferentiableAt ℝ f 0:=(readiness S L i).differentiableAt (by simp)
    exact (Push.side f he u).unique (hv.symm ▸ (Push.side f he T))
 rw [show fderiv ℝ (PressAt (F i)) 0 u= _ from he]
 have ht:(f ∘ K ∘ P) =ᶠ[𝓝 0] fun _=>0:=by
    have hu:Tendsto P (𝓝 0) (𝓝 0):= (show Continuous P from continuous_const.prodMk continuous_id).tendsto 0
    filter_upwards [hu.eventually (recouped X)] with r h; have hf:increment 1 (K (P r))= _:= (show _=FlightFlux.Broad X (P r) from h); change F i (increment 1 (K (P r)))= 0; rw [show increment 1 (K (P r))=_ from hf]; unfold FlightFlux.Broad; rw [show (P r).1=0 from rfl, G07.at_zero_increment]; let Z:=αLines F 1
    refine (congrFun (W 1 _) i).trans ?_; rw [stripeQ]; apply sum_eq_zero; intro j _; simp [αLines,v,cSignX]
 let D:= fderiv ℝ f 0
 have ht':HasDerivAt (K ∘ P) T 0:=by
    let x:= P 1; have hh := chord_K X; have hp:(fun t:ℝ=> t • x)=P:= funext fun i=> (by change i • ((0:tangD n),(1:ℝ))=(0,i); simp [smul_eq_mul])
    have h:=Push.side K (hh.differentiableAt (by simp)) x
    have he: fderiv ℝ K 0 x=T:=by rw [show fderiv ℝ K 0 x=_ from Chord_line X x]; change (1:ℝ) • _+0=T; rw [one_smul,add_zero]
    rw [he] at h; rw [←hp]; exact h -- likely occ
 have hy : HasDerivAt (f ∘ (K ∘ P)) (D T) 0:=by
    have hx: K (P 0)=0:=Chord_0 X
    exact (((readiness S L i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq _ ht' hx.symm)
 exact hy.unique ( (hasDerivAt_const _ _).congr_of_eventuallyEq ht)
-- valuations. scalar closures
variable {G:Genre}
abbrev entry_H (F:Paper n)(i:Wa n)(m:ℕ):=iteratedFDeriv ℝ m (PressAt (F i)) 0
abbrev crownx(G:Genre)(F:Paper n)(i:Wa n)(o:Seat n)(v:Confab o):ℂ:= (Nat.factorial G.orderB:ℝ)⁻¹ • entry_H F i G.orderB (fun _=>caster o v)
abbrev AccessD (G:Genre)(F:Paper n)(o:Seat n): Prop:=ready_D F ∧ (∀ i∉ (univ:Finset (Wa n)),F i=0) ∧ (∀ i j,j<G.orderB→entry_H F i j=0) ∧ ∀ i (v:tangD n),crownx G F i o (cast_P o v)= (Nat.factorial G.orderB:ℝ)⁻¹ • entry_H F i G.orderB (fun _=>v)
lemma matron (f:F∈ Glamor o G v)(w:300<n.val): AccessD G F o:=by
 obtain ⟨p,h,t,x,s,l,H,K,T⟩:= Glamor_votes f w; let A:=ready_D F; have he:=Glamor_S (o:=o) w G v F f; refine ⟨readiness _ H,fun i v=> (v (mem_univ _)).elim,?_,?_⟩
 · intro i j p'; cases G with
   | pure=>exact (Nat.not_lt_zero j p').elim
   | mixed=> rw [Nat.eq_zero_of_le_zero (show _ from Nat.le_of_lt_succ p')]; apply ContinuousMultilinearMap.ext; intro u; simp only [entry_H, iteratedFDeriv_zero_apply]; unfold PressAt; rw [G07.at_zero_increment,he.2]; rfl
   | gauge=>
      rcases i with _|i; swap; · rw [entry_H,he.1 i,show PressAt (0:Lit n)=fun _=>0 from rfl,iteratedFDeriv_fun_zero]; rfl
      change j<2 at p'; interval_cases j
      · apply ContinuousMultilinearMap.ext; intro u; simp only [entry_H,iteratedFDeriv_zero_apply]; unfold PressAt; rw [G07.at_zero_increment,he.2]; rfl
      let V:=AlphaY F; have hx:PressAt (F none)=TableF.term V:= funext fun i=> (bpu_T ..).2.symm; apply ContinuousMultilinearMap.ext; intro u; rw [entry_H,hx,iteratedFDeriv_one_apply, Axon.censored (sprig o H s l K) x.le]; rfl
 intro i q; let v:=caster o (cast_P o q); unfold crownx; apply congrArg ((Nat.factorial _ : ℝ)⁻¹ • ·)
 obtain ⟨a,b⟩:= torn_K q o w
 cases G with
 | pure=> rw [Genre.orderB,entry_H,iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]
 | mixed=>
    have ht:=micro_Mgrad _ H K a he.2 (q-v) b i; rw [map_sub,sub_eq_zero] at ht; change iteratedFDeriv ℝ 1 (PressAt (F i)) 0 (fun _=>v) = iteratedFDeriv ℝ 1 (PressAt (F i)) 0 (fun _=>q); rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply]; exact ht.symm
 | gauge=>
    rcases i with _|i; swap; · simp only [entry_H,he.1,Genre.orderB,show PressAt (0:Lit n)=fun _=>0 from rfl,iteratedFDeriv_fun_zero,Pi.zero_apply]; rfl
    let U:=AlphaY F; let r:= sprig o H s l K; have hp:PressAt (F none)=TableF.term U:=funext fun i=>(bpu_T ..).2.symm; have hz(i): ploy U q i= ploy U v i:=by
       have h':=ploy_nil r x.le a (q-v) i b; rw [map_sub,_root_.sub_apply,sub_eq_zero] at h'; exact h'
    have ht(i: tangD n): (fun _:Fin 2=> i) = ![i,i]:=by ext1 j; fin_cases j<;>rfl
    change entry_H F none 2 (fun _=>v)=entry_H F none 2 (fun _=>q); unfold entry_H; rw [ht,ht,hp,←ploy_iter,←ploy_iter,hz q,show ploy U v q=ploy U q v from ploy_herm r x.le _ _,hz]
end ArtCart
end MastTin
end YM.CF.XGarden
end
