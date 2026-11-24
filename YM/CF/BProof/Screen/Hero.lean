import YM.CF.BProof.Screen.Film
/-! Hero. prove Crafts for assembled F retaining complex measure -/
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Scene
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Scree Jet Vault Paige Drapes Pec Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {N:Side}{L₁ B₁ m₁:Side} {d₀:GramM (mid m₁ B₁)} {w R v:ℝ}{S:Gates.Stage d₀.funds w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(Y:S.Setup L a (More (mid m₁ B₁)) d y)(P:Entice S L a d y)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P d₀.path θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P d₀.path θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Loom (mid m₁ B₁)) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E θ Δ U ν δ} (Z : School Y d₀.path θ E Δ U ν δ rB)
open Prime Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil
open Prime Prime.Estate
open Palot Anthem Payment Oasis Stint TraceD
variable (K: Core j a₁ b l r (mid m₁ B₁)) (Ck:Clock Z k ξ){p:Odd L₁.val}{X: Pricing j L₁ p (Vault.Thread j)}(F:Grasp X B₁ δ)
variable {yv:Pay}{y₀ α A z Al Pz:ℝ}
variable (HK:Hinge F (Z.age P K) Δ.stage.c rateH Δ.stage.η yv d₀.J.I y₀ α A Al Pz)
local notation "I_"=> mid m₁ B₁
local notation "Code_"=> Hinge.Codes I_
variable (ht: Trust yv α Al z)
local notation "N_"=>mid m₁ B₁
local notation "Kℓ"=> Δ.stage.c
local notation "PR_"=> trueQ P Z K F d₀.J.I HK ht
local notation "Lθ"=>d₀.path
variable {v_:Pay}{wa βj a_g Cg h' o' ε':ℝ}(Gm:Oasis.Marks (Z.age P K) v_ Δ.stage.c rateH Δ.stage.η) {X':Cargo d₀ h' o'}(Tm:Pantry Gm X' ε')(Vb:Oasis.Tube d₀ v_ h' ε' o' a_g Cg)(ε:ℂ)(xw:Pouch Y P d₀.path θ)
-- fixed height Auth etc outsourced Lifted
local notation "οx"=> (F_' Y P d₀.path θ xw.val)
local notation "ψΘ"=> Z.pose P K
local notation "φΘ"=> Z.world1 P K
local notation "ΗΘ"=>Z.lineT.raw
variable (p₀:d₀.p.threshold=thresh y)(A₀:Spire.Pearl F)(v₀:u≤ A₀.q)
local notation "B0"=> fog_ P Z p₀ -- K and Et? 
local notation "QF"=> scoreP P Z k K F HK Gm Tm p₀
local notation "κcut"=> cutH P Z k K F HK Gm Tm p₀
open West Garden
local notation "Ψε"=> (fun xw'=>poleF P Z k K F HK Gm Tm ε xw' p₀)
local notation "Ξ"=> QF.M
local notation "χx"=> (tool Y xw.val)
local notation "FΧ"=> Cargo
local notation "ς"=> spores Y xw.val
variable (g:Fund₀ d₀ K A₀) (q:Δ.clock.nearM≤k) (pε: ε≠0) (vε:‖ε‖≤ε') -- pε collision
-- stutter phase Fξ fixed evaluate all f disclosures. verify masks `budget.power`. Frame actions price only via Guard. No Meas encl requirement yet.
def velvet (f:Fields I_):ℂ:= Complex.exp (κcut (tool Y xw.val)) * (purc d₀ οx (erase_ k xw.val) ε f * Complex.exp (-Charge.left mH (οx).1 B0+ (Manus.plumb HK Tm).rest mH k (φΘ xw)+Payment.changeFee d₀ QF Gm οx (ψΘ xw) (erase_ k xw.val) (Ζ_ xw.val) ε f))
local notation "PΞ"=>Ψε xw
lemma vehicle : velvet P Z k K F HK Gm Tm ε xw p₀ ς=poleF P Z k K F HK Gm Tm ε xw p₀:=rfl
variable (x'w:Pouch Y P d₀.path θ)
lemma stream_ (v:tool Y xw.val=tool Y x'w.val)(e:orbitL Y xw.val=orbitL Y x'w.val): velvet P Z k K F HK Gm Tm ε xw p₀= velvet P Z k K F HK Gm Tm ε x'w p₀:=by
 funext f; unfold velvet; have ht:= West.sameF_ P Z xw x'w v e; have hv:= West.here_eq P Z K xw x'w v e; have heq: erase_ k xw.val=erase_ k x'w.val:=congrArg (Trek.eraseBit mH g₀ k) (West.sick_ P xw x'w v e); have hy:framesL Y P d₀.path θ xw.val=Ζ_ x'w.val:= congrArg (Setup.color P Y d₀.path θ) v; rw [v,ht,hv,heq,hy, show φΘ xw=φΘ x'w from ?_]; exact Prod.ext (Prod.ext (show rawK xw.val=rawK x'w.val from congrArg Prod.fst ht) (congrArg sion hv)) (West.stund_ P Z xw x'w v e)
include g q pε vε Vb v₀
lemma quote_page : Complex.exp (κcut χx)*(ask d₀ F U QF οx (Ζ_ xw.val) (S.M y))= ∫ f:Fields N_,velvet P Z k K F HK Gm Tm ε xw p₀ f ∂gardenF I_:=by
 let I:= (pupil P Z k K F HK Gm Tm p₀ A₀ v₀ q xw); have ht: U οx= Tape.carried (ψΘ xw).val.1:=rfl
 rw [Payment.actualF U HK Tm Vb g pε vε ht (affords P Z k K F HK Gm Tm p₀) (by rfl) I,←integral_const_mul]; -- tune
 rfl -- potential R
local notation "Gp"=> globe mH y
variable (f:Pod Y→ℂ)(h:Envelope f) (lP:∀ x:Pod Y,¬Cabinet.Ready P Y d₀.path θ x→ f x=0) (xH:∀ x:Pouch Y P d₀.path θ,f x.val=poleF P Z k K F HK Gm Tm ε x p₀)
include h lP xH
lemma ticket : Payment.Crafts d₀ U QF (S.M y) θ S.κ S.P (Setup.soil P Y) (Brick.adapt mH g₀ f) (W:=F):=by
 refine ⟨Brick.adapt_m _ _ f h,?_,?_⟩; intro x p
 · unfold Brick.adapt; split; swap; · rfl
   rename_i u; apply lP; intro e; apply p; let M:=Brick.invert mH g₀ x; change Along P Y d₀.path θ x.1; rw [← show tool Y M=x.1 from congrArg Prod.fst (Brick.field_eq mH g₀ x u)]; exact e -- tune
 intro z p t
 let w:Along P Y Lθ θ z:= p
 let φ(s:Fields I_):= West.cardV P z t s w
 let i:= Classical.arbitrary (Fields I_); let e:=φ i
 have hv(s:Fields I_) : tool Y (φ s).val=z ∧ orbitL Y (φ s).val=t ∧ spores Y (φ s).val=s:= stems_ P z t s w
 have he: Set.EqOn (velvet P Z k K F HK Gm Tm ε e p₀) (fun s:Fields I_=>Brick.adapt mH g₀ f (z,t,s)) Set.univ:=by
    intro s h; unfold Brick.adapt; dsimp only; rw [if_pos (West.marked P z w), show f _=Ψε (φ s) from xH (φ s), stream_ P Z k K F HK Gm Tm ε e p₀ (φ s) ((hv i).1.trans (hv s).1.symm) ((hv i).2.1.trans (hv s).2.1.symm)]; exact Eq.trans (congrArg (velvet P Z k K F HK Gm Tm ε (φ s) p₀) (hv s).2.2.symm) (vehicle P Z k K F HK Gm Tm ε _ p₀)
 -- unify integrand one argument
 change Complex.exp (κcut z) * ask _ _ _ QF (area P Y Lθ θ z,t) (color P Y Lθ θ z) (S.M y)=_
 have hA: Seam.F_' Y P Lθ θ e.val = (area P Y Lθ θ z,t):=Prod.ext (congrArg (Setup.area P Y Lθ θ) (hv i).1) (hv i).2.1
 rw [← show cutH P Z k K F HK Gm Tm p₀ (tool Y e.val)= κcut z from congrArg (cutH P Z k K F HK Gm Tm p₀) (hv i).1, ← hA, ← show Ζ_ e.val=color P Y Lθ θ z from congrArg (Setup.color P Y Lθ θ) (hv i).1, quote_page P Z k K F HK Gm Tm Vb ε e p₀ A₀ v₀ g q pε vε]; exact integral_congr_ae (Eventually.of_forall fun i=> he (Set.mem_univ _))
end YM.CF.BProof.Scene
