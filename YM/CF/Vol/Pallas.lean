import YM.CF.Vol.Swell
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
variable {s':Signed} -- avoid sector precision orientation convention errors. actual deterministic gauge fine terms uses orient s
section earned
variable (T:Tube G S)(x:ℝ)(F: Forest S.ratio)(k:S.Choices)(j:Signed)(l:ℕ)
local notation "Rf"=>Stores.till x
local notation "RC"=> cart x S.patch.L
local notation "ℿ"=>fX T x F k j l
local notation "𝒱"=> vX T F k j
def parchF(i:Site f)(y:Ark T F):ℝ:= gplot (batch T.up.cubic Rf) (ℿ y) i+ gplot (batch T.up.quartic Rf) (ℿ y) i
def parchC(i:Site c)(y:Ark T F):ℝ:= gplot (batch T.down.cubic RC) (𝒱 y) i+ gplot (batch T.down.quartic RC) (𝒱 y) i
end earned
variable {σ γ:ℝ}{k:S.Choices}
set_option maxHeartbeats 600000 in
lemma ping(K:Teller G)(hp:P.Branches K.bind G)(hG:G.Simple)(n l:ℕ)(hn:3 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)) :∃ C ε:ℝ,0<C ∧0<ε ∧∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →sizedP G P K S T F →∀(k:S.Choices)(s:Signed), (∀ i,KnotP (parchF T x F k s l i) n 0 C ε)∧∀ i,KnotP (parchC T x F k s i) n 0 C ε:=by
 obtain ⟨C,V,b,hC,hV,hb,h⟩:=lift_paid hG K P hp n l (by omega) W; obtain ⟨D,hD⟩:=paint_supply G n
 let L(s:ℝ)(m:Side)(X:ℝ)(k:ℕ):=max 1 (X*atomCost G D s n k * (1+townCost G*countCost (entryWidth n m s))^n); let M:=1+Jet.composeCost n C 1; have hM:0<M:=by unfold M Jet.composeCost; positivity; -- true
 let Y:=Jet.composeCost n; let A(k):= Y (L K.top.width P.L K.top.paths k) M; let U(k):= Y (L K.below.width 1 K.below.paths k) 1; let E:=max (A 3+A 4) (U 3+U 4); let ε:=min (min b 1) (1/M);
 have hE : 0<E:=by apply lt_of_lt_of_le _ (le_max_left ..); unfold A Y L Jet.composeCost; positivity
 refine ⟨E,ε,hE,lt_min (lt_min hb zero_lt_one) (by positivity),?_⟩
 filter_upwards [h] with x hX c f S T F h hv k t
 obtain ⟨z,hz,hg,hp⟩:= hX S T F h hv; let B:= sol S T k x F l; let P':=pulse B; let R:= (Uniform.partSpace (Primary c G) (Key F G)).symm.toContinuousLinearMap; let X:=R ∘ P'
 have hT u (hu:‖u‖< min b 1): Jet.Allows n P' u M := gum ((hp k u.1 ((norm_fst_le u).trans_lt (hu.trans_le (min_le_left ..)))).1) ((hu.trans_le (min_le_right ..)).le)
 have hx u (hu:‖u‖< min b 1): Jet.Allows n X u M:= ((hT u hu).linear _ meets_n).mono (one_mul _).le
 have hm:P' (0:Ark T F)=0:=by simp [P',pulse,B,(hp k 0 (by simpa)).2.1] -- tune
 have hB:X 0=0:=by simp [X,hm]
 obtain ⟨C,D,h₁,h₂⟩:=h.funds.1.feeds
 have hu:‖(0:Ark T F)‖< min b 1:=by rw [norm_zero]; positivity
 have hy{j:ℕ}(hj:3 ≤ j)(i:Site f)(A':ℕ→ Atom G j)(hA: SumBudget (fun i=>(A' i).budget K.top.width) K.top.paths): KnotP (fun y=>gplot A' (fX T x F k t l y) i) n 0 (A j) ε:=by
    let q:=choice t k; let g(z:Positions (Joint F G)):=gplot A' (signedFine F z t) i; let v(z:Ark T F):=gplot A' (Jazz T q t z) i
    have H w(hw:‖w‖<1): Jet.Allows n g w (L K.top.width P.L K.top.paths j):= (paper (floorZ A' hA K.top.width_pos hD w hw t i)).mono (le_max_of_le_right (by rw [← h.got]; exact le_rfl))
    have he:cFoot 3 v:=by
        obtain ⟨h1,h2⟩:= asp hA K.top.width_pos hj t i
        let B:=Prod.snd (α:=Bid.Dir G c) (β:=Bid.Dir G f); exact capZ (fun U _=>gplot A' U i) T q t F ((h1.of_le le_top).comp (f:=B) (0:LogsP G c f) contDiffAt_snd) (ride_eps (h1.of_le le_top) B contDiffAt_snd rfl h2).1
    have hf:ContDiffAt ℝ (3:ℕ) v (0:Ark T F):=by apply (((H _ (show ‖R 0‖<1 by simp)).order hn).smooth.comp (f:=R) 0 R.contDiff.contDiffAt)
    refine knot3 ((ride_eps hf P' (((hT _ hu).order hn).smooth) hm he).1) le_rfl fun y hy=>?_ -- tune
    have hY:‖y‖< min b 1:= hy.trans_le (min_le_left ..); have hC:=miles (x:=y) (f:=X) (show 1 ≤ n by omega) hx ((norm_nonneg _).trans_lt hu) hY; rw [hB,sub_zero] at hC -- tune sub_zero
    exact (H _ (hC.trans_lt ((mul_comm ..).trans_lt ((lt_div_iff₀ hM).1 (hy.trans_le (min_le_right ..)))))).comp (f:=X) (hx _ hY)
 have hc:=h.size
 have he{j:ℕ}(hj:3≤ j)(i:Site c)(A':ℕ→Atom G j)(hA:SumBudget (fun i=>(A' i).budget K.below.width) K.below.paths): KnotP (fun y=>gplot A' (vX T F k t y) i) n 0 (U j) ε:=by
    have hk:2 ≤ c.val:=by omega
    let S:= (Tree.select (cubeF c) (show Odd (cubeF c).count.val from ⟨0,rfl⟩)).some; let g(z:Mast G c):= gplot A' (pull t 0 (facadeX G z)) i
    obtain ⟨h1,h2⟩:= asp hA K.below.width_pos hj t i
    let F': Ark T F →L[ℝ] Mast G c:= ContinuousLinearMap.fst ℝ _ _
    let P:= (tint G _).toContinuousLinearMap.comp F'
    have hK:cFoot 3 (g ∘ F'):= (ride_eps (h1.of_le le_top) P P.contDiff.contDiffAt P.map_zero h2).1
    refine knot3 hK le_rfl fun y hy=>?_; let u: Ark T F →L[ℝ] Positions (Joint S G):= upperCol.comp F'
    have hx z':‖u z'‖≤ ‖z'‖:=by change ‖meetVar z'.1 0‖≤ ‖z'‖; rw [norm_meet]; exact max_le (norm_fst_le _) (by rw [norm_zero]; positivity)
    have hU: ‖u y‖<1:=(hx y).trans_lt (hy.trans_le ((min_le_left ..).trans (min_le_right ..)))
    have H:=floorZ A' hA K.below.width_pos hD (u y) hU t i
    refine (((paper H).mono (le_max_right ..)).comp (f:=u) (Jet.allows_linear (L:=u) (show ‖u‖≤1 from ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (hx i).trans_eq (one_mul _).symm) hU.le)).germ ?_
    filter_upwards with z; rw [show u z= upperCol (F' z) from rfl,tia hk S]; rfl
 constructor
 · intro i; exact ((hy (j:=3) le_rfl i _ (barn h₁.three _)).addV (hy (j:=4) (by omega) i _ (barn h₁.four _)) (by unfold ε; positivity) (by omega)).mono (by norm_num) (le_max_left ..) le_rfl
 intro i; exact ((he (j:=3) le_rfl i _ (barn h₂.three _)).addV (he (j:=4) (by omega) i _ (barn h₂.four _)) (by unfold ε; positivity) (by omega)).mono (by norm_num) (le_max_right ..) le_rfl
end YM.CF.Vol
