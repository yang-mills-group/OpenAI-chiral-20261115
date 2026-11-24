import YM.CF.Cour.Rite
import YM.CF.Cour.Route
import YM.CF.Pec.Ora
import YM.CF.Souk.Rayon
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Hors Newt Souk RG Push Pressure
open Next.SectorChange AnalyticBridge.MarginalMultiplier3b1d Next.SectorChange.Wisps
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {ι:Type}[Fintype ι]{B L:Side}{n k j:ℕ}{e t x u C A:ℝ}
variable {p:Clip}{q: Gauge}{c f:Side}
open Pec
local notation "GG"=>group
variable{m X:Side}{T:Roam m X B}{H: Tube group T}{F: Forest T.ratio}{G: Ratio (CSide m B) (CSide X B)}
variable {h:Odd L.val}{Y:Pricing j L h (Thread j)}{P:Grasp Y B e}{K:Teller GG}
abbrev Msca (m X B:Side)(G:Ratio (CSide m B) (CSide X B))(e:ℝ):= Seal (Site (More (CSide X B)))→ Broc.Rent0 G e→ℂ
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
structure Tally(T:Msca m X B G e)(Φ:nomA m X B→ℂ)(s K a C:ℝ)(n:ℕ):Prop where
 members: ∃ N:Seal (Site (More (CSide X B)))→ℝ,(∀ i,Jet.Flash (Broc.dressL G e) (Jet.LineE n G K e) n i (T i) (N i)) ∧ ∀ i,hitE a N i ≤ C
 even(v:nomA m X B)(h:v∈Broc.Rent0 G e): Φ v=∑ i,T i ⟨v,h⟩
def fence(O: Msca m X B G e)(p:0<e)(r:ℕ)(y:nomA m X B):ℂ:=∑ i∈univ.filter fun i:Seal (Site (More (CSide X B)))=>i.card ≤ r,O i (Pec.pear G p y)
section
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma crisp {z} (K:Teller GG) (P': Patch)(hx:0<e)(o l:ℕ)(n:ℕ)(k':T.Choices)(hn:2 ≤ n){α γ C p D a w:ℝ}(hc:Cert P' K T H x)(O: Msca _ _ B G e)(M:Male)(U:Dress (CSide X B))(I:Pride (CSide X B))(R:Pride (CSide _ B))(hp:Tally O (shipA G P M U I R) γ C a w n)(hf:T.ratio=ratio G)(hg:Fleck G hx F γ C n)(hy:0 < γ)(hd:0<a)(hv:0≤w)(hs:0 ≤ D)(ht:0 ≤ p)(hq:p ≤1)(hM:GoodsR F (sol T H k' x F l) (Uniform.station z) (temp x) D p)
 (h:cFoot 3 (myth G F z H.low H.down P M U I R α)) (hy':0<temp x): let t:= temp x
 let K':= safeD H.down (cart x T.patch.L); let Z:=fence O hx o ∘ Laic.hats F; let Y(y:Mast GG (More (CSide _ B))):= Z (flute F (sol T H k' x F l) t y)- α • secondM H.low H.down (tint GG _ (t•y)); let A:= w*(Real.exp ((a/2)*T.patch.L.val))*countCost (a/2); let v:= A*Real.exp (-(a/2)*o)
 pierce Y (2*(p*A+2*p*((D+1)*A)+(D*v+D*(D*v)))):=by
 intro t K' Z Y' A v; obtain ⟨s,u,hz,hE⟩:= hc.funds.1.feeds; rw [← hc.funds.1.low] at hE; obtain ⟨N,M',X'⟩:=hp.members
 let L:=univ.filter fun i:Seal (Site (More (CSide X B)))=>i.card ≤ o; let D'(i):=O i ∘ frameT G hx F; let W:= ∑ i,D' i
 let R': Snap F→ℂ:= shipA G P M U I R ∘ Laic.hats F
 have he:W=ᶠ[𝓝 0] R':=by
    filter_upwards [ball_mem_nhds 0 hy] with y ht; let H:=hg.onP _ (mem_ball_zero_iff.mp ht); unfold W D' R'; simp only [Function.comp_apply,Finset.sum_apply,frameT,Pec.pear_even G hx H]; exact (hp.even _ H).symm
 have hh(i): W i-Z i= ∑ j∈ Lᶜ,D' j i:=by unfold W Z fence; rw [Finset.sum_apply, ← Finset.sum_add_sum_compl L]; change ((∑ j∈L,D' j i)+_)-(∑ j∈L,D' j i)=_; abel
 have hZ: Cour.Funds Z A:=by have ht:= sleeve hx hf hg N O M' 0 L (fun _ _=> Nat.zero_le _) hn hy X' hd; rw [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at ht; exact ht -- tune
 have hF: Cour.Funds (W-Z) v:=by rw [show W-Z= (fun i=>∑ j∈Lᶜ,D' j i) from funext hh]; apply (show w*(Real.exp (-(a/2)*o)* Real.exp ((a/2)* T.ratio.count.val))*countCost (a/2)=v from by unfold v A; change w*(Real.exp _* Real.exp (_* T.patch.L.val))* countCost _=_; ring) ▸ (sleeve hx hf hg N O M' o Lᶜ (fun i hi=> by simp only [L,mem_compl, mem_filter,mem_univ,true_and] at hi; omega) hn hy X' hd) -- tune
 have hA:0 ≤ A:=by unfold A; have ht:= Uniform.count_pos (half_pos hd); positivity
 let L':Mast GG (More (CSide m B))→L[ℝ] Vox m B:= (tint group _).toContinuousLinearMap.comp (t • ContinuousLinearMap.id ℝ _)
 have hg: ContDiffAt ℝ 2 (secondM (n:=CSide m B) H.low H.down) (L' 0):=by rw [map_zero]; exact (sane hE).of_le le_top
 have H':ContDiffAt ℝ 2 (fun y=> α • secondM H.low H.down (L' y)) 0:=(hg.comp (f:=L') _ L'.contDiff.contDiffAt).const_smul _
 let P':=flute F (sol T H k' x F l) t; let V:=flute F (Uniform.station z) t; let D':=Z ∘ P'; let E'(y):=α • secondM H.low H.down (L' y); let f:= W ∘ V
 have hK:= pick hM hZ hF hq hA (mul_nonneg hA (Real.exp_pos ..|>.le)) hs ht; obtain ⟨hV,hx',hD,hW,hM⟩:=hM; change P' 0= 0 at hV; change V 0=0 at hx'
 let hO:ContDiffAt ℝ 2 D' 0:=(show ContDiffAt ℝ 2 Z (P' 0) from hV.symm ▸ hZ.stiff).comp 0 hD; have hf':ContDiffAt ℝ 2 (D'-E') 0:= hO.sub H'
 change pierce (D'-E') _; refine ⟨hf',fun i=>?_⟩
 let B'(y):= shipA G P M U I R (Laic.hats F (V y))- E' y
 have hg: D'-f+(f-E')= D'-E':=by abel
 have hu:ContDiffAt ℝ 2 (f-E') 0:=by
    have hx:f-E'=D'-E'-(D'-f):=by abel
    rw [hx]; exact hf'.sub hK.1 -- adjust
 have ht: B'=ᶠ[𝓝 0] (f-E'):= ((show Tendsto V (𝓝 0) (𝓝 0) from hx' ▸ (show Tendsto V (𝓝 0) (𝓝 (V 0)) from hW.continuousAt)).eventually he).mono fun j t=> congrArg (·-E' j) t.symm -- tune
 have he:Uniform.entry (D'-E') 0 i=Uniform.entry (D'-f) 0 i:=by
    rw [← hg]; unfold Uniform.entry; rw [iteratedFDeriv_add_apply (f:=D'-f) (g:=f-E') (hK.1.of_le (by norm_num)) (hu.of_le (by norm_num)),_root_.add_apply]; erw [← (ht.iteratedFDeriv ℝ 2).eq_of_nhds]; exact add_eq_left.mpr (draw_s _ F z hx _ _ _ _ _ _ _ α _ h hy' i (hu.congr_of_eventuallyEq ht)) -- tune
 rw [he]; exact hK.2 i
end
end YM.CF.Cour
