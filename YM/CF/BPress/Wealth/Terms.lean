import YM.CF.BPress.Wealth.Storm
/-! Coordinates on heavy supports. Every kept can read via whole `tickets=inside depot`; control adjacent Hall. Delay to cloak level and PL counts by column.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth} (X:Bands s b) (M:ℕ) (d:Clip)(p:BudgetPoint)
local notation "Bond" => BPress.Link
open SU
lemma heavy_on (R:PathData group)(β:ℝ) (h:Checks M p d)(i:Root s)(U V: Config group s)(v:Set.EqOn U V (tickets M i)): heavy R d p β M i U=heavy R d p β M i V:=by
 rcases i with i|⟨u,i⟩; · have he(k:Fin 4): U (aperture i k)= V (aperture i k):= v (mem_image_of_mem (aperture i) (mem_univ k)); apply congrArg (fun x:group.El=> β*PathData.clipped d p.threshold (group.chord x)); rw [faceValue,faceValue, Travel.price _ _ _ U,Travel.price]; change U (aperture i 0)*U (aperture i 1)*(U (aperture i 2))⁻¹*(U (aperture i 3))⁻¹= V (aperture i 0)*V (aperture i 1)*(V (aperture i 2))⁻¹*(V (aperture i 3))⁻¹; simp_rw [he] -- Travel restricted group? yes! revise
 apply keep_local R β u i h U V; intro i a b; exact v (inside_iff ..|>.mpr ⟨a,b⟩) -- group link? inside handles support only
open SU
lemma canon_agrees {J:Type*}[Zero J] (S: Root s)(u:High b M)(g:retained X M S)(x y: Bills X J)(h: Set.EqOn x y ((fun i:X.Air=> i.1) ⁻¹' (danger X M S))): Set.EqOn (raw X x) (raw X y) (tickets M S):=by
 intro i p; unfold raw; cases l : edgeKey X i with|none=> simp| some a=> exact h (show a∈ (_) from (show a.1∈danger _ _ _ from ticket_key u S g p l)) -- tune notation parent

variable (β:ℝ) (q:Sheet.Atlas)
lemma effects (h : High b M){y:ℝ} {U V W W':Micro s}{K K':Bills X E}(p:Mission X y K W U)(p':Mission X y K' W' V) {i:Root s}(g:retained X M i)(e:Set.EqOn W W' (tickets M i))(f:Set.EqOn K K' ((fun i:X.Air=> i.1) ⁻¹' (danger X M i))): Set.EqOn U V (tickets M i):=by
 intro j h'; have ht := inside_le (near_zone h i g) (ticket_mem M i h'); rw [Mission.narrates p _ _ ht,Mission.narrates p' _ _ ht]; unfold anglePaid angleBeg; rw [e h']; cases l:edgeKey X j with| none=>rfl| some a =>rw [Option.elim_some,Option.elim_some,f (show a∈_ from ?_ )]; exact ticket_key h i g h' l -- tune rw e first

lemma high_purchase (G:GapSize)(M:ℝ→ℕ) (p:PL fun y=> (M y:ℝ)) (t:∀ᶠ y in atTop,1≤ M y): ∀ᶠ y in atTop, High (G.select y) (M y):=by
 have ht:NPL (fun y=>temp y^2 * (M y:ℝ)):= (npl_power npl_temp 2 (by omega)).mul p
 -- want `(M +1) t^2 small`. n ≤ P; P=n+2ω. n/4. consume 20M,8,4 extra. estimate P≥ t^-2.
 let W : ℝ:=2*G.collar; let f(y:ℝ):ℝ:= 4*(5*M y+2)+4+W
 have he:NPL (fun y=> f y*temp y^2):= PL.times ((((PL.const 4).mul (((PL.const 5).mul p).add (PL.const 2))).add (PL.const 4)).add (PL.const W)) (npl_power npl_temp 2 (by omega))
 filter_upwards [he.drop.eventually (gt_mem_nhds zero_lt_one),G.tail_P,G.bounds,t,eventually_gt_atTop (0:ℝ)] with y v t h m u; have ht:=h.2.1; rw [←t] at ht; let k:= G.select y; have hz: f y ≤ (k.P:ℝ):= by have h:= temp_pos u; change _ ≤ ((G.select y).P:ℝ); apply le_trans _ ht; rw [inv_pow, ←one_div]; exact (le_div_iff₀ (by positivity)).mpr v.le
 have hh : 4*(5*M y+2)+4+2*k.collar ≤ k.P:= by
    change 4*(5*(M y:ℝ)+2)+4+2*G.collar ≤ _ at hz; rw [show k.collar=G.collar from rfl]; exact_mod_cast hz
 refine ⟨m,?_,?_⟩; change _ < k.marked.val; unfold BandWidth.P at hh; omega; change _ ≤ k.marked.val/4; unfold BandWidth.P at hh; omega

def counted (M D:ℕ) := (2*(8*M+D)+1)^4 * Fintype.card (Option Signed × PlaqAxes)
lemma counted_PL (D:ℕ) (M:ℝ→ℕ) (p:PL fun y=> (M y:ℝ)): PL (fun y=>(counted (M y) D:ℝ)):=by
 unfold counted; push_cast; apply PL.mul _ (PL.const _); exact ((((PL.const 2).mul (((PL.const 8).mul p).add (PL.const _))).add (PL.const 1)).pow 4)

-- Tickets ports
variable {K:Bills X E}{W U:Micro s}{κ y:ℝ}{i:Root s}(G: Mission X y K W U)(T: ToneNoise y W)(u:retained X M i)(H:High b M)
include H G T u
lemma tests_soft (e:κ*temp y< q.δ)(f:regular (M:=M) (X:=X) (chosen X κ y K) i)(j:Link s)(p:j ∈ tickets M i): chord (U j) (actuated y (canon X (softAl X κ y K q)) j) ≤ xi y:=use_core κ y e q rfl G T j (fun _ v=> use_reg H f u p v) (inside_le (near_zone H i u) (ticket_mem M i p)) -- tune
lemma costs_soft (v: 0≤κ*temp y)(f:regular (M:=M) (X:=X) (chosen X κ y K) i)(j:Link s)(p:j ∈ tickets M i): chord (U j) (background y j) ≤ xi y+κ*temp y := near_back κ y v G T j (fun k t=> use_reg H f u p t) (inside_le (near_zone H i u) (ticket_mem M i p))
end YM.CF.BPress.Wealth
