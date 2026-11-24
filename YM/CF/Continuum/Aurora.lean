import YM.CF.Continuum.TiltLimits

/-!
# Relative price around one holonomy (torus correlation), cofinal pivots.
Next use it to stop at **one** pivot, and perform detection in the UV limit.
Cost statement with all sites simultaneously. Path volume range restrictions
in `Pastures`; not extending to arbitrary volumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Mint.Roe Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 8192
variable {N : ℕ→Side} {a b c w η r e K b' v C' l s' L' μ y h C L0 γ vA r₀ C₀:ℝ}{J B m:Side}{O:Odd J.val}{j k n₀:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P} {x L L1 : ℕ→ℝ}
namespace Pastures
local notation "NP" => (fun i=> mid (N i) B)
local notation "M" => More ∘ NP
local notation "n" => eur NP
local notation "N'" => eur (More∘NP)
variable {I : ∀ i,GramM (mid (N i) B)} (D:Pic.Span hP K b' v C' l s' k)
    (Z: Pastures B N x h C r μ L' w γ L0 L I)
set_option quotPrecheck false
local notation "β'" => (fun i=>(I i).beta)
include Z D
local notation "t_u" i:max => compassRate (NP i) (hemp x i)
local notation "billY" i:max => Real.exp (-stoutY (M i) (β' i) (4*hemp x i) γ (tame x i) L' L0)
local notation "yield" i:max => gainS (M i) (hemp x i)*billY i
local notation "hest" i:max => horn (NP i) s'
local notation "Yt" i:max => yieldAngle (I i) (t_u i)
local notation "billX" i:max => Real.exp (flagBill (NP i) (L i) (L i) C - kinetic (M i) (I i).p L' L0 (β' i) w)
local notation "A_ψ" i:max => Kea.angel (N i) P (I i).J.M
local notation "ηΩ" i:max => ‖normalizedTilt P (t_u i) (I i)‖
local notation "shotW" i:max => compass (NP i) (t_u i)
variable (X:∀ i,Loom (mid (N i) B))(u:∀ᶠ i in atTop,SkinT (I i) (X i) e)(H:Port D a y C₀ vA r₀ n₀)(h₀:C₀≤h)
omit D
lemma narrowTilt : ∃ x':ℕ→ℝ,Aqua (eur NP) x' ∧ ∀ᶠ i in atTop,0<x' i ∧∀ U:Pane (mid (N i) B), flags (I i).p.threshold U=∅→ 0< reflectible (mid (N i) B) (t_u i) U→∃ F:Cart (More (mid (N i) B)),lawnK (gauge F U) (Kea.tax (needles (mid (N i) B))) (x' i):=by
 obtain ⟨xP,K,v,k,hQ⟩:=towards; have he:=Z.path; have hv:Aqua n (tame x):=Z.large.tame_bills; let G:= n
 let t(i):=t_u i; have hp:Gray G N':=by apply Gray.eqK ((Gray.arg Z.tend).mul (Gray.coef Z.tend 2)); exact Eventually.of_forall fun i=>by norm_num [eur, More, G]
 have ht:Aqua G t:=by let H:= (hemp x); have hu:Aqua G H:=hv.clip Z.tend (Z.path.helm.mono fun i ⟨u,v,w⟩=> ⟨u.le,(by linarith only [u,w])⟩); exact Aqua.fed hu ((Gray.coef Z.tend 10).mul hp) Z.tend
 let Y(i):=xP*t i+400*N' i^2*(K*tame x i); refine ⟨Y,(ht.fed (Gray.coef Z.tend xP) Z.tend).panel ((hv.fed (Gray.coef Z.tend K) Z.tend).fed ((Gray.coef Z.tend 400).mul (hp.powG Z.tend 2)) Z.tend),?_⟩
 filter_upwards [Z.path.helm,Z.path.infl, Z.support0] with i ⟨p,h,l⟩ ⟨a,b,c,d⟩ o; have ht: 0<t i:= mul_pos (by positivity) p; refine ⟨by unfold Y; positivity,fun U v p=>?_⟩; exact hQ (NP i) U (tame x i) _ c (o.1 ▸ v) ht p
omit Z in
private lemma absolute_gray {A:ℕ→ℝ} (h:Aqua n A) : Aqua n fun i=> |A i|:=by
 intro j; have ht := (h j).abs; rw [abs_zero] at ht; exact ht.congr (fun i=>by rw [abs_mul,abs_of_nonneg (pow_nonneg (by unfold eur; positivity) j)])
include D H h₀ u
-- objective: relative ratios by normalizedTilt weight restore probability. Norm denominator variation paid here global. Still high.
theorem income : ∃ f:ℕ→ℝ, Aqua n f∧∀ᶠ i in atTop, (ηΩ i)>0 ∧∀ (F:GlowLeg)(s:Site (mid (N i) B)), ‖moment (recX P (I i) (X i)) (shotW i * glowRead F s) - comparedToTilt F (I i) s (t_u i) P‖ ≤ f i * ηΩ i := by
 obtain ⟨Y,Q,U⟩:=narrowTilt Z; let y0:= n; let A:= bloom NP r x; let B0(i):= baton (NP i) (L i) (A i) C a; obtain ⟨C0,z,v0,W⟩ := tilted D Z; let t(i):= inPocket (n i) (B0 i) y a C' (Y i) K; let g(i):=C0*n i^z; let f(i):=(|t i|+ 90* (billX i/(yield i*hest i)))*g i
 have he:=Z.tend; obtain ⟨hV,hB⟩:= Pastures.surge Z a; let ζ(x):= Gray.coef he x; let ζp:= Gray.arg he; have hf:Aqua y0 t:= Aqua.panel ((hV.pays (ζ y) he).pays (ζ _) he) ((Q.fed ((ζ C').mul (ζp.powG he 10)) he).pays ((ζ 45).mul ((ζ 1).add he (((ζ K).mul ζp).powG he 2))) he)
 refine ⟨f,(((absolute_gray hf).panel ((harvestRatio D Z).fed (ζ 90) he)).pays ((ζ C0).mul (ζp.powG he z)) he),?_⟩
 filter_upwards [he.eventually_ge_atTop n₀,Z.flagK D H,U,u,W,Z.path.helm, Z.path.infl,Z.support0,yields_ω D Z,hB,(Q.shrinks.eventually (ge_mem_nhds one_pos)), (Q 10).eventually (ge_mem_nhds (show 0 < min v vA from lt_min D.xP H.knot))] with i ℓ hKz ⟨p,V⟩ ht ⟨v1,v2⟩ ⟨p',_,pC⟩ ⟨a1,a2,a3,a4⟩ ⟨xz,w1,w2,w3,v3,k3⟩ ⟨Yb,Y'⟩ ⟨e,_⟩ xQ pQ
 refine ⟨v2,fun F s=>?_⟩; let n':=NP i; let W:=I i; let X1:= ηΩ i; have hv'(X) (t:flags W.p.threshold X=∅) : Graph.HelpP X (A i) r:=tile_p X a3.le Z.wind.le (xz ▸ t) -- tune namespace & more t
 have hZ:=harvest F D W (X i) ht s w1 H h₀ Z.bold hKz Z.clip w3 (show 0<A i from lt_add_of_pos_of_le a3 (by positivity)) (Nat.cast_le.mp ℓ) w2 a2.le e Z.wind.le Z.size p xQ ((pQ.trans (min_le_left ..))) (pQ.trans (min_le_right ..)) V hv' (mul_pos (by positivity) p')
 let L0:= Yt i; let Q0:= L0 * A_ψ i; have hQ:0<Q0:=by nlinarith only [Yb,Y']
 let E:= billX i/(yield i*hest i); have hE:0≤E:= div_nonneg (Real.exp_pos _).le Yb.le
 apply hZ.trans; have ht':Q0 ≤ g i*X1:= v1; refine le_trans ?_ (show (|t i|+90*E)*(g i*X1)=f i*X1 from Eq.symm (mul_assoc ..)).le; rw [add_mul]; unfold E at *; have hz:X1=ηΩ i:=rfl
 change (Yt i)* (t i*A_ψ i)+45*billX i ≤ _; apply add_le_add
 · rw [mul_left_comm]; exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hQ.le) (mul_le_mul_of_nonneg_left ht' (abs_nonneg _))
 rw [mul_assoc 90]; calc
   _ = 45*(billX i/(yield i*hest i)*(yield i*hest i)):=by rw [div_mul_cancel₀ _ Yb.ne']
   _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (show yield i*hest i ≤ 2*(g i*X1) from Y'.trans (mul_le_mul_of_nonneg_left ht' (by norm_num))) hE]
end Pastures
end YM.CF.Window
