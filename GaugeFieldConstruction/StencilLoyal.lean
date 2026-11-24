import YM.SU5.Registration.Ink.Potential
/-!
 # Reference frame alignment for Ink with the Actual purchases: link even the specific phase-embedding used in the reconstruction. Versus a different gram-based injection that might intertwine costs with Main but not constitute the existing pole.

 Root layer: prove recapture of the Carton field vectors by the absolute corner protocol of `Fields/Tall` (needed later for NSF.Boundary not just this duplicate version). No damped approximation price hypotheses. Account from actual coherences and strong limits over the given radial domain.

 Proof compares heatCup for Small symbols with a corresponding heatKick on root. Doesn't just compare `expect`: that could still let the subspace correspondences differ. Develop Poin camera etc as in `YM/SU5/{Registration/Ink,FiniteGaugeData/Poin}` but for vector equality. On this cross budget c: unify all strict positive Eu pad stamps too.
 -/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option maxRecDepth 2600
noncomputable section
namespace YM.SatinWFixed.Carton
open Filter Function Set MeasureTheory Spectral Mink Boundary Boundary.Small OS Complex OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin SatinRegistration
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{V : Type*} [AddCommGroup V] [Module ℂ V] {n:ℕ}
variable (B: Carton S V)
private lemma heated_st {y:ℝ} {p:ℝ≥0} (t : (p:ℝ) < y) : let r:= y-(p:ℝ);
 ripZ S (↑y*I) p 0=S.E r.toNNReal:=by
 let r:= y-(p:ℝ); have h:0<r:= sub_pos.mpr t
 have he: bufferF 0=0:= Subtype.ext (by apply Mink.ext_by <;> simp [bufferF]); change _= S.E r.toNNReal;
 unfold ripZ; rw [he,S.uZero,ContinuousLinearMap.comp_id];
 have hp: interval (↑y*I) p=duration r.toNNReal:=by apply Complex.ext <;> simp [Small.interval, duration,Real.coe_toNNReal r h.le]; rfl
 rw [hp,S.roots_heat (Real.toNNReal_pos.mpr h)]
lemma start_gapSt (p:ℝ≥0)(z:Points n)(y:Heights n)(i: Fin n)(h:(p:ℝ)<y i) :
 ripZ S (Boundary.shift z y i) p (Boundary.trace z i)= S.E ((y i-(p:ℝ)).toNNReal)*M S (z i):=by
 let b:=z i; let w:ℂ:= ↑(y i)*I; let k:= (y i-(p:ℝ)).toNNReal; have ht:Boundary.shift z y i=w+(YM.time b:ℂ):=by unfold w b Boundary.shift; rw [add_comm]
 have he:Boundary.trace z i=0+ YM.spatial b:= (zero_add ..).symm; have hp: (p:ℝ) < w.im:=by simpa [w] using h
 ext1 u; rw [ht,he,SatinRegistration.heat_commutes S k b|>.eq,rip_shift w p 0 b u hp]; exact congrFun (congrArg DFunLike.coe (heated_st (S:=S) h)) u|> congrArg (M S b) -- tune rip_shift args order explicit `(x:=)`?
lemma train_filmSt (p:ℝ≥0)(v:Fin (n+1)→ V)(z: Times (n+1))(x: SpacePoints (n+1)) :
 B.bar p (v 0) (B.trainZ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0))=Rail (fun i=> B.bar p (v i)) (fun i j=>ripZ S (z j-z i) (p+p) (x j-x i)) B.omega:=by
 induction n with
 | zero=> rw [Rail_step,s1P,mul_one]; rfl
 | succ n ih=> nth_rw 1 [Rail_step]; rw [s1S]; let v':= Fin.tail v; let z':= Fin.tail z; let x':= Fin.tail x; change B.bar p (v 0) (ripZ S (z' 0-z 0) (p+p) (x' 0-x 0) (B.bar p (v' 0) (B.trainZ p n (Fin.tail z') (Fin.tail x') _ (z' 0) (x' 0))))=_; rw [ih]; rfl
private lemma filmPay_st {R:Type}[Monoid R]{α:Type}(X:α→R)(J K:α→α→R){r:α→α→Prop}(h:∀ i j,r i j→ J i j= K i j)(L:List α)(t:L.Pairwise r) : Film X J L = Film X K L:=by
 induction L with
 | nil=> rfl
 | cons i l ih=> rw [Film_step,Film_step, ih t.of_cons]; congr 2; cases l with
                                                                      | nil => rfl
                                                                      | cons j l=> exact h i j ((List.pairwise_cons.mp t).1 j (List.Mem.head ..))
noncomputable abbrev inkShot_st (p:ℝ≥0): ∀ n, (Fin n→V)→ Heights n→Points n→ H
  | 0,_,_,_=> B.omega
  | n+1,v,y,k => let z := Boundary.shift k y; let x:= trace k; ripZ S (z 0) p (x 0) (B.bar p (v 0) (B.trainZ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))
lemma shotLeg_st (p : ℝ≥0) (v: Fin (n+1)→V)(y: Heights (n+1)) (h:ample p y)(x : Points (n+1)) : B.inkShot_st p (n+1) v y x=S.E ((y 0-(p:ℝ)).toNNReal) (pitch S (fun i=> B.bar p (v i)) (fun i j=> S.E (fareGap y p i j)) x B.omega):=by
 let z:=Boundary.shift x y; let b:= Boundary.trace x; change ripZ S (z 0) p (b 0) (B.bar p (v 0) _) = _; rw [B.train_filmSt p v z b, start_gapSt p x y]
 · let v':=(y 0-(p:ℝ)).toNNReal; change S.E v' (M S (x 0) _) = S.E v' _
   apply congrArg (S.E v'); let F(i):= B.bar p (v i); let D(i j:Fin (n+1)):= S.E (fareGap y p i j); let G:=fun i j:Fin (n+1)=>ripZ S (z j-z i) (p+p) (b j-b i); let Z(i j:Fin (n+1)):=M S (-x i)*D i j* M S (x j)
   have hc:Rail F G=Rail F Z:= filmPay_st F G Z (fun i j (v : i<j)=> by
      unfold G Z; have he: ((p+p:ℝ≥0):ℝ) < y j-y i:=by push_cast; linarith [h.1.2.2 i j v, p.coe_nonneg]
      rw [ripZ_gap p y x i j he]; unfold D; rw[← SatinRegistration.heat_commutes S (fareGap y p i j) (-x i)|>.eq,mul_assoc,tgo, add_comm (-x i), ← sub_eq_add_neg]) (Each ..) (List.pairwise_lt_finRange _)
   change M S (x 0) (Rail F G B.omega) = Rail (fun i=> optx S (F i) (x i)) D B.omega; rw [hc,Rail,Rail,Each,List.finRange_succ]; exact (Into S _ F D _ B.stay _ _).symm
 linarith [h.2 (0:Fin (n+1)),p.coe_nonneg]
lemma loyalPay_st (p:ℝ≥0)(v:Fin n→ V)(y: Heights n) (f:Joint n): Integrable (fun x: Points n=> f x • pitch S (fun i=> B.bar p (v i)) (fun i j=> S.E (fareGap y p i j)) x B.omega) := by
 let F:=fun i=> B.bar p (v i); let T:= (fun i j=> S.E (fareGap y p i j)); let x(p:Points n):= pitch S F T p; let y(p:Points n):= x p B.omega
 have ht : Continuous y:= shops S F T id continuous_id _ continuous_const
 obtain ⟨r,t⟩:= fee S F T; apply (f.integrable.norm.mul_const r).mono' (f.continuous.smul ht).aestronglyMeasurable; filter_upwards with p;
 change ‖f p • x p B.omega‖≤_; rw [norm_smul]; let z:= B.omega -- syntax!
 have hc: ‖x p B.omega‖≤r:= by simpa [z,B.size] using le_trans ((x p).le_opNorm z) (mul_le_mul_of_nonneg_right (t p) (norm_nonneg _))
 exact mul_le_mul_of_nonneg_left hc (norm_nonneg _) -- tune if no abs right
lemma horizonInk_st (p:ℝ≥0)(v:Fin (n+1)→ V)(y: Heights (n+1))(h:ample p y)(f:Fin (n+1)→Test4): (∫ x: Points (n+1), Joint.materialize (n+1) f x • (B.inkShot_st p (n+1) v y x))=
 S.E ((y 0-(p:ℝ)).toNNReal) ((B.lateFilm v f (fareGap y p) (fun _=>p) (Each _) B.vacuum).val):=by
 let F:=fun i=> B.bar p (v i); let T:= (fun i j=> S.E (fareGap y p i j)); let K:= Joint.materialize (n+1) f; let z(x:Points (n+1)):= K x • pitch S F T x B.omega; let M:= ((y 0-(p:ℝ)).toNNReal)
 rw [tonight]; have hz:Integrable z:= B.loyalPay_st p v y K; rw [show (fun x:Points (n+1)=>Joint.materialize (n+1) f x • B.inkShot_st p (n+1) v y x)=(fun x=> S.E M (z x)) from (by funext x; rw [B.shotLeg_st p v y h]; exact (map_smul (S.E M) (K x) _).symm)]; rw [(S.E M).integral_comp_comm hz]; apply congrArg (S.E M); apply ext_inner_left ℂ; intro u; have he:= Poin.orches S u B.omega F T f; rw [←integral_inner hz]; change (∫ x, inner ℂ u (z x))=_; simp_rw [z,inner_smul_right]; exact he -- type args tune
-- logD→0 and t>0; prove true corner. for any v Carton.
noncomputable abbrev heatKick_st (b: MarkWords V)(t:ℝ) := ∫ x : Points b.length,(Joint.materialize b.length (fun i=>(b.get i).2) x) • B.inkShot_st (logD t) b.length (fun i=>(b.get i).1) (profile t b.length) x
private lemma log_to_zeroSt : Tendsto logD till (𝓝[>] (0:ℝ≥0)):=by
 refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within logD ?_ (Eventually.mono (show ∀ᶠ x in till, 0<x from self_mem_nhdsWithin) (fun t h=> (suitable (n:=0) (show 0<t from h)).1.1)); have he:Continuous logD:=by unfold logD; fun_prop
 exact (show logD 0=0 from (by simp [logD])) ▸ (he.tendsto _).mono_left nhdsWithin_le_nhds
private lemma profileGap_st (i j:Fin n): Tendsto (fun t:ℝ=> fareGap (profile t n) (logD t) i j) till (𝓝 0):=by
 let F(t:ℝ):= fareGap (profile t n) (logD t) i j; have he:Continuous F:= continuous_real_toNNReal.comp (by unfold profile logD; fun_prop)
 exact (show F 0=0 from (by simp [F, logD, fareGap, profile])) ▸ (he.tendsto _).mono_left nhdsWithin_le_nhds
lemma atCorner_st (L:MarkWords V): Tendsto (B.heatKick_st L) till (𝓝 (B.row L).val):=by
 cases L with
 | nil=> have h:B.heatKick_st []=fun t:ℝ=> B.omega :=funext (fun t=>by unfold heatKick_st; simp only [List.length_nil,Points.volume_nil]; rw [integral_dirac]; change Joint.trivial _ • _=_; rw [Joint.trivial_at,one_smul]); rw [h]; exact tendsto_const_nhds
 | cons v L=>
    let b:=v::L; let p:=fun i:Fin (L.length+1)=>(b.get i).1; let f(i:Fin (L.length+1)):=(b.get i).2; let U:= Each (L.length+1); let g(t:ℝ):=fareGap (profile t b.length) (logD t); let D(t:ℝ):=(profile t b.length 0-(logD t:ℝ)).toNNReal
    have hp(t:ℝ)(u:0<t): B.heatKick_st b t= (stoveAt S (D t) (B.lateFilm p f (g t) (fun _=>logD t) U B.vacuum)).val:= B.horizonInk_st _ p (profile t b.length) (suitable u) f
    have hc:Continuous D:= continuous_real_toNNReal.comp (by unfold profile logD; fun_prop); have ht: Tendsto D till (𝓝 0):= (show D 0=0 from (by simp [D,profile,logD])) ▸ (hc.tendsto _).mono_left nhdsWithin_le_nhds
    have he := B.morning p f (J:=0) U till (fun s _=> logD s) (fun _=>log_to_zeroSt) g (fun i j=> profileGap_st i j) (P:=fun _=>B.vacuum) (x:=B.vacuum) (by intro k; simp [Grading.budget,Grading.due]) -- check
    have hg := Grading.Approaches.hilbert (bands S) (through_heat S till _ ht he)
    rw [stoveAt_zero,B.play p f] at hg; unfold U Each at hg; rw [show ((List.finRange (L.length+1)).map fun i => (p i,f i))=b from (List.ofFn_eq_map ..) ▸ List.ofFn_get b] at hg -- equation syntax
    exact hg.congr' (Eventually.mono (show ∀ᶠ x in till, 0<x from self_mem_nhdsWithin) (fun t q=>(hp t q).symm))
#print axioms atCorner_st
end YM.SatinWFixed.Carton
end
