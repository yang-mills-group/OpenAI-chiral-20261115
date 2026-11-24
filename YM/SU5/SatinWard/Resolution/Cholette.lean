import YM.SU5.SatinWard.Resolution.Carter
import YM.SU5.SatinWard.Resolution.Qilin
import Anomaly.Cover.Chiral
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Tapestry
open SlabMark Papal Papal.Moon Papal.Moon.Moonlit SwitchC Garland Terrace Juniper
namespace CasaF
open Swell Sonar Fock Tapestry.StageW LitCurrent LitCurrent.Chamber
open QuadClock Preparation.Tabletop
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)(s:ℕ)(i k:ℕ→ℕ) {r v:ℕ} {a b φ:ℝ} (A:∀ n,s<Y.uv (k n))
variable (X:∀ n,MaskPoint Y r s (i n) (k n) a b)(E:(n:ℕ)→eraτ Y s (i n) (k n) r a φ)
local notation "N" j:max=> side Y (i j) s
local notation "Yt"=> tent Y H
local notation "R"=> (Y.meter.a s)
local notation "S✩"=> pavilion (nodeC (0:Cover)) ((Y.meter.a s).B+12)
local notation "p_" j:max=> RootBook Y (i j) (k j) s
local notation "M✔" j:max=> (Y.voyage (i j)).CapeT s
local notation "V"=> LitCurrent.expiry (4*a) φ
open Rill
-- Occurrences both Q(x) and J^i(x) at SAME root, build V (two linked mask trees as in Lampro,E). On all ℰ valuations along this one path, after Pose.stays.NO sampling independently.
abbrev Visit := Option Axis
abbrev nearSprite (Y:Course Λ (VolumeCape.Dream.Nimbus l))(D:Division){a b:ℝ}{i k s j:ℕ}(E:eraτ Y s i k j a b) (i':Visit)(x:Site (side Y i s)):= i'.elim (qField Y E x D) (fun v=> JField Y E x D (v,false))
variable (D:Division)(p:0<a)
local notation "X₀"=> nodeC (0:Cover)
include A X
lemma epoch_one_s (j:ℕ): (p_ j).p =Y.meter.a s:= (prices_plot Y s (i j) (k j) (A j).le).1
lemma enc (u:Visit)(n:ℕ)(x:Site (side Y (i n) s)): AtSupport false (offsetMask ((R).B +12) x) (nearSprite Y D (E n) u x)∧covariant (nearSprite Y D (E n) u x):=by
 have hk:=X n; rw [← epoch_one_s Y s i k A X n]; let Vb:=(p_ n).p; let Vx:= hat Λ.R.L Λ.x s; cases u with
 | none=>
    let B:= (Vb.B/10); let I:= grantA D (E n) x; let T:= gaugeWindow x hk.C.roof hk.C.angle (totals I hk.C.hint (show moored _ I from LitCurrent.Pattern.moorA (E n) x) B).1 hk.C.threshold hk.C.extra hk.C.hint.le; let P':=(T.scale Complex.I).scale (↑(qHull Λ.R.L Vx):ℂ); exact ⟨P'.ticket,P'.rolls⟩
 | some v=>
    obtain ⟨b,P',q⟩:= cameo D _ _ _ (1/2) x (E n) hk.C (v,false); let g:= (P'.scale Complex.I).scale (↑(jHull Λ.R.L Vx):ℂ); exact ⟨g.ticket,g.rolls⟩
omit X A
private lemma scale_menu {T:ℕ→ Type*}[∀ i,NormedAddCommGroup (T i)][∀ i,NormedSpace ℂ (T i)] {M:(i:ℕ)→PairsC→T i} (p:Menu M)(q:ℂ): Menu (T:=T) (fun i x=> q • M i x):=(Menu.cnst (fun _=>q) (norm_nonneg _) (fun i=>le_refl _)).scale p
include X A
variable (pc:Finset Cover)
include p
lemma museumS (w:Visit): Menu (T:=fun j=> FC (Single (side Y (i j) s))) (fun j z=>nearSprite Y D (E j) w 0 (replant pc (side Y (i j) s) z)):=by
 have h(j:ℕ):Roof (N j) Λ.J.k Λ.d Λ.J.n (M✔ j):= (X j).C.roof; let o(j:ℕ):Site (N j):=0; let f(j:ℕ)(a: PairsC):= (replant pc (N j) a).1; have hv(j:ℕ): (p_ j).p= R:= epoch_one_s Y s i k A X _; let B:= (Y.meter.a s).B/10
 let P:=hat Λ.R.L Λ.x s; have hT(U:(j:ℕ)→StageTree (N j) Λ.d (4*a) φ)(T:∀ j,moored (node (o j)) (U j)): Menu (fun i x=>traceMeter R (M✔ i) (o i) (beforePing (U i) B) (f i x)) ∧ Menu (T:=fun i=> FC (Single (N i))) (fun i x=> spinMark R (M✔ i) (o i) (beforePing (U i) B) (f i x,f i x)):= by
    let W:= X 0; let F:= beforePing (U 0) B; have hG:= (totals _ p (T 0) B).1; have hp: (R).threshold≤ Λ.J.k:=by rw [← hv]; exact W.C.threshold
    have hc:B+Λ.J.n+10 ≤ (R).B:=by unfold B; rw [← hv]; exact W.C.extra
    apply verve_t f (regraft pc) (fun i=>(measurable_fst.comp (replant_b ..))) h (fun j=> (totals _ p (T j) B).1) hp hc p.le Λ.dpos
    let h':= gaugeWindow (o 0) (h 0) Λ.dpos hG hp hc p.le; exact (norm_nonneg _).trans (h'.price (1,1))
 let H0: Menu (X:=PairsC) (I:=ℕ) (T:=fun i=>FC (Single (N i))) (fun i _=>1):= Menu.cnst (fun _=>1) zero_le_one (fun _=>by simp)
 cases w with
 | none=>
    let T:= (hT (fun i=>grantA D (E i) 0) (fun i=> LitCurrent.Pattern.moorA (E i) (0: Site (N i)))).1; let K:= Menu.scale T H0
    apply Menu.congr (scale_menu (scale_menu K Complex.I) (↑(qHull Λ.R.L P):ℂ)); intro i x; unfold nearSprite qField; -- issue i shadow
    simp_rw [hv]; rfl
 | some v=>
    obtain ⟨P',Q'⟩:=hT (fun i=>grantJ D (E i) (0,(v,false))) (fun i=>LitCurrent.Pattern.moorJ (E i) (0,(v,false)))
    let U:= Menu.add Q' (scale_menu (Menu.scale P' H0) (-(↑(1/2:ℝ)):ℂ))
    apply Menu.congr (scale_menu (scale_menu U Complex.I) (↑(jHull Λ.R.L P):ℂ)); intro w z; unfold nearSprite JField
    simp_rw [hv]; let g:=replant pc (N w) z; let P':= live (M✔ w) R B (o w) (grantJ D (E w) (0,(v,false))) g.1
    change (_:ℂ) • (Complex.I • (StressExchange.preJ _ P'+(-(↑(1/2:ℝ)):ℂ) • (P'.trace • 1)))= (jHull Λ.R.L P:ℂ) • (Complex.I • preHalf (1/2) (Dial.tickA _) P'); rw [preHalf, neg_smul, sub_eq_add_neg] -- ambiguous
private lemma encoded(n:ℕ)(u:Visit): Aligns (nearSprite Y D (E n) u):=by
    have hx(y): AtSupport false univ (nearSprite Y D (E n) u y):= (enc Y s i k A X E D u n y).1.mono (subset_univ _)
    cases u with
    | none=> exact poised (qTurns Y (X n) (E n) D) hx
    | some v'=>
       change Aligns (fun x=>JField Y (E n) x D (v',false))
       exact lyrical (M:=fun v x =>JField Y (E n) x D (v,false)) v' (beatTurns Y (X n) (E n) D) hx
lemma decidedAs (U:∀ j:ℕ,Roomy S✩ (side Y (i j) s)):
 ∃ (L:ℕ→ℕ)(Z: Visit→ℕ→Family (tent Y H))(W:Visit→ Family (tent Y H)), StrictMono L ∧ ∀ p:Visit,BQueue S✩ (Z p) (W p) ∧ Neutral (tent Y H) (W p) ∧ (∀ j, Neutral (tent Y H) (Z p j)) ∧ ∀ j x, exhibit Y H s (i (L j)) (carriage x (Z p j))=nearSprite Y D (E (L j)) p (wrap (side Y (i (L j)) s) x):= by
 let M(i':Visit)(j):=nearSprite Y D (E j) i' (0:Site (N j)); let T:= S✩; have hq(j:ℕ)(p:Visit):AtSupport false (Satin.region S✩ (N j)) (M p j) ∧ covariant (M p j):=by
    let h:= enc Y s i k A X E D p j 0; unfold Satin.region; rw [wrap_pav,←node_of,map_zero]; exact h
 obtain ⟨F,h',u⟩:=organized Y H s i T M U (fun u i=>hq _ _) (museumS Y s i k A X E D p S✩)
 obtain ⟨L,t,ν,tu,a⟩:= (h'.closure.isCompact_of_isClosed isClosed_closure).isSeqCompact (x:=F) (fun j=> subset_closure (Set.mem_range_self _)); let Z':= F∘ν; let MZ(p):= render T Yt (L p);
 have ht(p): Tendsto (fun i=> Z' i p) atTop (𝓝 (L p)):= tendsto_pi_nhds.mp a p
 refine ⟨ν,fun p i=>render T Yt (Z' i p),MZ,tu,fun u'=>⟨?_ ,?_ ,fun i=>(u _ u').2,?_⟩⟩
 · exact queue_V _ (ht u')
 · exact (harmonicHere (S:= T)).2 (fun W=> continuousColor _ _ W (ht u') (ht u') (Eventually.of_forall (fun i=>(harmonicHere (S:=T)).1 ((u _ u').2) _))) -- tune names include binder.P.S
 intro j x; let M(y):= nearSprite Y D (E (ν j)) u' y; let W:= render T Yt (Z' j u'); have hx(y): AtSupport false univ (M y):= (enc Y s i k A X E D u' _ y).1.mono (subset_univ _)
 have hP:exhibit Y H s _ W= M (wrap _ (0:Cover)):=by rw [map_zero]; exact (u _ u').1
 have hF : Aligns M :=encoded Y s i k A X E D p _ u'
 let b:= exhibit_carriage Y H s (i (ν j)) (M:=M) (p:=0) hF hP x
 rwa [zero_add] at b -- tune let dependent.F.Rpl
#print axioms decidedAs
end CasaF
end YM.CF.Buffered.Afterglow.Tower
