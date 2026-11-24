import YM.SU5.Reconstruction.Oblique.RollStep
import YM.SU5.Reconstruction.Oblique.Bows
/-! # sharp/history identity including Tilt. bare and assembled at all resolvers. Don't conclude positivity from this! -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
-- open only necessities
open Wilson FullBill Tapestry Tapestry.Altitude Spark
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (P:Ramp)
-- witness on χ unselected prior and every inspected period
variable (i k s:ℕ)
section
local notation "M" => Y.uv k
local notation "ν" => side Y i M
local notation "X" s:max => ((Y.voyage i).X (Y.uv k)).gram s
local notation "T" => Y.meter.a M
local notation "YT" s:max=> (Y.voyage i).CapeT s
local notation "PU"=> Λ.U
local notation "Zn" => capP (K:=Λ.K) PU ((X M).beta) (T) (m:=mesh (Y.ir i) Λ.R.L M)
lemma angleB_steel(v:Pane (side Y i (Y.uv k))) : Spire.arum (P.vehicle ν) false true (Dial.mateK ν) (Zn v)= Zn (P.turnLink ν v):=by
 have h: JetS P.plan.s false true P.reel:= P.jet
 change Spire.arum (prepU P.plan P.reel (xtra false) _) _ _ _ _= Zn (stir (xtra false) P.plan v)
 let v':=stir (xtra false) P.plan v; let R : Set (Pane ν):={v|flags (T).threshold v = ∅}
 unfold capP; by_cases p:v∈R
 · rw [Set.indicator_of_mem p, Set.indicator_of_mem (show v'∈R from (PhaseChoice.stillMask P.plan v).mpr p),arum_scale,
       change_g Λ.W.pearl Λ.V.note (Λ.J.gran.trans ((Y.voyage i).ownership M).size) (show 1≤Λ.K.j by rw [Λ.kJ]; decide) v (PhaseChoice.guardedTop Y i k v p) babyM P.plan false P.reel h,PhaseChoice.basic_move]
   apply congrArg (· • _); change star (Complex.exp _) = _; rw [Complex.exp_eq_exp_ℂ,star_exp]; simp [Complex.exp_eq_exp_ℂ]
 rw [Set.indicator_of_notMem p, Set.indicator_of_notMem (show v'∉R from mt (PhaseChoice.stillMask P.plan v).mp p)]
 nth_rw 1 [←zero_smul ℂ (0:Phys ν)]; rw [arum_scale,show cSignX _ (0:ℂ)=0 from star_zero _,zero_smul]
lemma steel_reads(x: Mark (side Y i (Y.uv k))): markedRead (P.bill x) (YT M) (denZ (X M) Λ.U (YT M))=star (markedRead x (YT M) (denZ (X M) Λ.U (YT M))):=by
 let Z:=denZ (X M) Λ.U (YT M); let D(g:Mark ν)(v:Orbit ν):= letterRead (g (drawn (YT M) v)) (Z v); let G:=P.bill x
 change (∫ v,D G v∂city ν)= (starRingEnd ℂ) (∫ v,D x v∂city ν); rw [← integral_conj,← (P.tilt_mp).integral_comp' (D G)]; apply integral_congr_ae; filter_upwards [P.roof_angles (YT M) (Papal.roofage Y i M)] with v p'
 let U':=P.vehicle ν
 let J:=Spire.arum U' false true (Dial.mateK ν)
 have hy:Z (P.slantOrbit ν v)=J (Z v):=by
      unfold Z; change denZ _ _ _ (P.slantOrbit ν v)=_; rw [Y.whole,Y.whole]; exact (angleB_steel Y P i k v.1).symm
 have ht:G (P.both ν (drawn (YT M) v))=Spire.tourP U' false true (x (drawn (YT M) v)):=by unfold G Ramp.bill; rw [P.retrace]; rfl
 unfold D; change inner ℂ (Dial.mateK ν) (acts (G _) _) = _; rw [show G _=_ from (show G (drawn (YT M) (P.slantOrbit ν v))=_ from (congrArg G p').trans ht),hy]; unfold J; rw [← arum_act U' false true]; set B:=Dial.mateK ν
 nth_rw 1 [← arum_self (q:=B) U' false true (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR P.plan inert P.reel P.jet ν)] -- tune
 exact arum_globe U' false true (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR P.plan inert P.reel P.jet ν) _ _
lemma steel_calc(x:Mark (side Y i (Y.uv k))): Journey.compass Y i k (Y.uv k) (P.bill x)=star (Journey.compass Y i k (Y.uv k) x):=by
 have h:= steel_reads Y P i k 1; rw [show P.bill (1:Mark (side Y i (Y.uv k)))=1 from funext fun _=>theta_one _,markvac] at h; unfold Journey.compass; rw [star_div₀,steel_reads]; exact congrArg _ h -- target fn tune
-- casts, Steps in THIS Grant
lemma displays {A B:Side}(h:A=B)(f:Mark A) : Tapestry.arrange _ _ h (P.bill f)=P.bill (Tapestry.arrange _ _ h f):=by subst B; rfl
lemma exhibits(F:Family (tent Y H)) : exhibit Y H s i (P.cuspF (tent Y H) F)=P.bill (exhibit Y H s i F):=displays P _ _ -- args s shadow
lemma ascends (p:Satin.PairIdx Y s i k){f:Mark (side Y i s)}(u:AtSupport false Finset.univ f):
    ascender Y s i k (P.bill f)= P.bill (ascender Y s i k f):=
 Ramp.RampRise (Vale.apt (Y.ir i) Λ.block Λ.R.L s) (patternA Y s i k) Λ.K.j (patternQ Y s i k).val _ Λ.R.odd_side _ _ (patternβ Y s i k) _ P ((fullness Y i k p.1).cap_grant.aligned s p.2) u ((fullness Y i k p.1).cap_grant.branch s p.2) ((Y.voyage i).ownership s).paid (legal Λ) (threshold Y).1 (threshold Y).2
lemma all_steps (z:Tapestry.Pay Y s i k){f:Mark (side Y i s)}(q:AtSupport false univ f): Journey.compass Y i k s (P.bill f)= star (Journey.compass Y i k s f):=by
 -- s draws out of current M
 suffices h:∀ t:ℕ,∀{s:ℕ},∀ (e:t+s=M){f:Mark (side Y i s)} (q:AtSupport false univ f), Journey.compass Y i k s (P.bill f)=star (Journey.compass Y i k s f) from h (M-s) (Nat.sub_add_cancel z.2) q
 intro t; induction t with
 | zero=> intro s v f _; rw [Nat.zero_add] at v; subst s; exact steel_calc Y P i k f
 | succ t ih=>
    intro s e f p; have ht:Satin.PairIdx Y s i k:= ⟨z.1,by omega⟩
    rw [partake Y s i k ht ((P.term_marked p).mono (Finset.subset_univ _)), ascends Y P i k s ht p]
    exact (ih (show t+(s+1)=M by omega) (PhaseChoice.ascender_paid Y i k ht p)).trans (congrArg star (partake Y s i k ht p).symm)
local notation "K" => tent Y H
lemma every_step (p:Tapestry.Pay Y s i k){F:Family (tent Y H)}(h: TestFamily K true F): sharp Y H s i k (P.cuspF K F)=star (sharp Y H s i k F):=by
 rw [actualRead,actualRead,exhibits]; exact all_steps Y P i k s p (safeNat Y H s i (⟨F,h⟩: Dome K))
end
-- unselected strong solve. not coselected.
section
variable {m n:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H m n I E)
local notation "K"=> tent Y H
include V in
lemma stepRow {F:Family (tent Y H)}(p:TestFamily K true F) : I s (P.cuspF K F) i= star (I s F i):=by
 have h:=V.together s F p; have u:=V.together s (P.cuspF K F) (aux_test (P.faces K p.paid.choose_spec)); exact tendsto_nhds_unique_of_eventuallyEq (u.inner i) (h.inner i|>.star) ((V.pick.pass Y H s i).mono fun _ q=> every_step Y H P i _ s ⟨q.depth,q.enters⟩ p)
include V in
lemma step_Price {F:Family (tent Y H)}(p:TestFamily K true F): E s (P.cuspF K F)=star (E s F):=by
 have h:= V.together s F p; have u:=V.together s (P.cuspF K F) (aux_test (P.faces K p.paid.choose_spec)); exact tendsto_nhds_unique_of_eventuallyEq u.periods (h.periods.star) (Eventually.of_forall fun i=> stepRow Y H P (m i) s V p)
end
end YM.CF.Buffered.Afterglow.Tower.Tilted
