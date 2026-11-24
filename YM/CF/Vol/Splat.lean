import YM.CF.Vol.Pots
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows Stack
-- direction map scales before CL
abbrev meal (F:Forest S.ratio)(x:ℝ): Fish (Key F G) →L[ℝ] Directions G f:= LinearMap.toContinuousLinearMap ⟨⟨trays S x F, trays_add⟩,trays_smul⟩ -- tune
lemma meal_n(F:Forest S.ratio)(x:ℝ)(z : Fish (Key F G)): ‖meal F x z‖ ≤ shade G*‖z‖:=by
 let f:=tint G _ z; apply le_trans ?_ (tint_le z); change ‖fresh x (shots S x) (bareStores S) F (tape (leaveX F x z))‖ ≤ ‖f‖; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; unfold fresh; split; next hi=> split <;> rename_i hv; exact norm_le_pi_norm f (⟨i,hi⟩:F.Free); simp
 all_goals rw [norm_zero]; exact norm_nonneg _
-- barrel pricing
lemma ships (p:Clip)(L C D:ℝ)(n:ℕ)(h:0<s)(hp:0≤ C)(hr:0≤ D):∃ M:ℝ,0<M ∧∀{c:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](V:E → Config G c)(Y:E→ LogArray G (Cell c))(x:E), (∀ i, Allows n (fun y=> G.mat (V y i)) x D)→(∀ i,Allows n (fun y=> Y y i) x C)→∀ P:PathData G,∀ {a},P.Bounds p s L a→∀ r i, Allows n (fun y=>barrel P r (V y) (Y y) i) x M:=by
 obtain ⟨N,hN,H⟩:=travel_coupon G n D hr (half_pos h); let B:=G.colorScale⁻¹*(2^n*(2^n*N*(G.colorScale*C))*N); have hB:0≤ B:=by unfold B; have := G.colorScale_pos; positivity
 refine ⟨max (L*B) 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩
 intro c E _ _ V Y x ht hA P a hQ r i
 simp_rw [Stack.finite_price _ _ _ _ hQ]; refine (allows_sum (s:=Stack.allShort r) (C:=fun l=> |Stack.grouped P i.2 l| * (B*Real.exp (s*l.length))) (fun u hu=>?_)).mono ?_
 · let X:=Real.exp (s/2*u.length); have he:= adjoint_cost ((travel_jets ht i.1 (w:=u.walk) (Nat.le_add_right u.walk.length 4)).mono (H _)) (hA (slotFace u i.1)); -- tune
   refine ((he.smul _).mono ?_); rw [show Real.exp (s*u.length)=X*X by unfold X; rw [← Real.exp_add]; congr 1; ring]; exact Eq.le (by unfold X B Slot.length; ring)
 conv_lhs=> arg 2; intro i; rw [mul_comm B,← mul_assoc]
 rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right (Stack.grouped_le _ hQ i.2) hB).trans (le_max_left ..)
def dragB(T:Tube G S)(x:ℝ)(k:S.Choices)(u:Pot S G)(i:Slots S):= Rows.bump T x (horseA S G u) k u.2 i
set_option maxHeartbeats 500000 in
lemma drip(K:Teller G)(P:Patch)(hp:P.Branches K.bind G)(n:ℕ)(hv:3 ≤ n+1)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1)) :∃ C ε:ℝ,0<C ∧0<ε ∧∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch=P → K.Funds S T →∀ x:ℝ,∀k:S.Choices,∀ u:Pot S G, ‖u‖<ε → ∀ i, Allows n (fun y=> dragB T x k y i) u C:=by
 obtain ⟨M,hM,h⟩:= postU W.labels -- allows n+2
 -- get actual Q, not tide. yes
 let r:=predictionRadius P G K.bind (n+1) W.lc M W.D W.δ W.r; let t:= Uniform.composeCost (n+1) W.W (connectorCost P G (n+1) W.lc M); let Y(t:ℝ):= (2:ℝ)^n*Uniform.composeCost n t 1
 let B:= max 1 (Y (curvatureCost G*travelCost G (n+1) 4 M)); have hB:0<B:=zero_lt_one.trans_le (le_max_left ..)
 let D:=Uniform.composeCost n M 1; have hD: 0<D:=by unfold D Uniform.composeCost; positivity
 let A:=curvatureCost G*(2^(n+1)*t*(Uniform.composeCost (n+1) t 1)); let Q:= max 1 (Y A); have hQ:0<Q:=zero_lt_one.trans_le (le_max_left ..)
 obtain ⟨X,hX,H⟩:=ships (G:=G) K.top.clip K.top.paths B D n K.top.width_pos hB.le hD.le
 let R:= Real.sqrt K.bind.penalty*Q; let F:= Real.sqrt K.top.clip.direct*B; let C:= max (max X R) F
 refine ⟨C,if 0<r then min r 1 else 1,hX.trans_le ((le_max_left ..).trans (le_max_left ..)),by split; exact lt_min (by assumption) zero_lt_one; exact zero_lt_one,?_⟩
 intro c f S T hP ht x k u hx i; obtain ⟨s,i|i⟩:=i <;> let Z:=hoop S G s <;> have hU:= (h S).2 s <;> let K':=(choice s k) <;> let L: Pot S G →L[ℝ] Pot S G:= (ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _) <;> have hi: ‖L‖≤ 1:= (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; change max ‖i.1‖ ‖(0:Directions G f)‖≤_; exact max_le (norm_fst_le _) (by simp)) <;> have hp₀:=prediction_radius_pos S hU (show 2 ≤ n+1 by omega) W.exp W.log W.focus <;> rw [ht.knobs,hP] at hp₀ <;> rw [if_pos hp₀] at hx <;> have hv:‖u‖<1:=hx.trans_le (min_le_right ..) <;> have hL:‖L u‖ ≤ ‖u‖:=(L.le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) hi)
 · have he(j) : Allows n (fun y:Pot S G=> plaquetteJet S (horseA S G y) s j y.2) u B:=by
      let g(y:Pot S G):= G.curvature (faceValue (Z y) j); refine ((clnk (g:=g) (E:=Mast G c) u hv.le (C:=curvatureCost G*travelCost G (n+1) 4 M) (curvature_price (U:=fun y=>faceValue (Z y) j) (x:=L u) (travel_jets (U:=Z) (fun i=>(hU.2.2 _ _ (hL.trans hv.le)).order (by omega)) _ (a:=4) le_rfl)) ).mono (le_max_right ..)) -- tune
   unfold dragB; simp only [bump, Sum.elim_inl,faceKick]; split
   · obtain ⟨a,b,hX,hY⟩:= ht.feeds; have hh (y:Bond f): Allows n (fun z:Pot S G=> G.mat (facade S s (horseA S G z) 0 y)) u D:=by
        exact ((hU.2.2 y (L u) (hL.trans hv.le)).order (show n ≤ n+1+1 by omega)).comp (f:=L) (allows_linear hi (hL.trans hv.le))
     exact (H _ _ _ hh he _ hX _ _).mono ((le_max_left ..).trans (le_max_left ..))
   rw [ht.high]; have hh:= (he i.1).smul (Real.sqrt K.top.clip.direct); rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hh; exact hh.mono (le_max_right ..)
 let g(y:Pot S G):= G.curvature (predictorTurn (horseA S G y) k s i y.2)
 have hm : Allows (n+1) (fun z:Pot S G=> G.mat (S.prediction (Z z) K' i)) (L u) t:=by
    have hw:= prediction_pay S hU (show 2 ≤ n+1 by omega) W.exp W.log W.focus (L u) (mem_ball_zero_iff.mpr ((hL.trans_lt hx).trans_le ?_)) K' i
    · unfold t; rw [show P=S.patch from hP.symm]; exact hw -- t local!

    rw [ht.knobs,hP]; exact min_le_left ..
 have hh:L (L u)=L u:=rfl; have hw: Allows (n+1) g (L u) A := curvature_price (U:=fun y=>predictorTurn (horseA S G y) k s i y.2) (hm.times (by
    let f(y:Pot S G):= S.prediction (Z y) K' i; exact ((show Allows (n+1) (fun y=>G.mat (f y)) (L (L u)) t from hh.symm ▸ hm).inverse (f:=f) |>.comp (f:=L) (allows_linear hi ((hh ▸ hL).trans hv.le)))))
 have hPix: Allows n (bzoom g) u Q:= (clnk u hv.le hw).mono (le_max_right ..)
 unfold dragB; simp only [bump,Sum.elim_inr,noiseKick, ht.knobs]
 have hz:= hPix.smul (-Real.sqrt K.bind.penalty); simp only [neg_smul, abs_neg,abs_of_nonneg (Real.sqrt_nonneg _)] at hz; exact hz.mono ((le_max_right ..).trans (le_max_left ..))
end YM.CF.Vol
