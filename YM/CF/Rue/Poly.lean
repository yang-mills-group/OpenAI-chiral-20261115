import YM.CF.Rue.Pry
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
open Jet Forge Eire Pressure.Tube Esti Cloak Rill Hake
attribute [local instance] opCStarAlgebra
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{s t C B u w:ℝ}{k:ℕ}
local notation "G₀"=>SU.group
variable {n m:Side}(S:StepData n (More m))(x:ℝ)(T:Tube G₀ S)(q:Chi)(d:ℝ)(l:ℕ)
variable (R:GramM m)(M:Monk G₀ S)(F:E→ Config G₀ n)
local notation "M_"=>hallU S F M
local notation "U_"=> (fun y=> (M_ y).sent x T q d l R.beta)
variable{S}
abbrev paperT (q:Chi)(k:ℕ)(C D:ℝ):Prop:=∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{n:Side}(U:E→ Pane n)(T F: Finset (Cell (More n)))(P:ℝ),0<P → F ⊆ T → (∀ i∈F,Tender (fun t=> faceValue (U t) i) x (C*P) k) →
 let G'(z):=∏ i∈F, padK (fun t=>faceValue (U t) i) q P z; Allows k G' x (Cloak.priceK k T.card D) ∧ (x∈tsupport G' → ∀ i∈F, Pressure.toll (U x) i < P)
abbrev WrapG (k:ℕ)(σ C v:ℝ):Prop:= ∀{m:Side}{H:BudgetPoint}(o:Hub m), H.order=k→ H.threshold ≤ σ →∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](V:E→ Pane m)(x:E)(I: Finset (Bond (More m))), (∀ j:Bond (More m),Skye.ends j⊆ o.val.2 → Tender (fun y=> V y j) x (C*H.threshold) k) → (∀ j:Bond (More m),Skye.ends j⊆o.val.2 → j∉I → ∀ᶠ y in 𝓝 x,V y j=V x j) →∀ (Ψ: Pane m→ℂ)(K:ℝ), LocalOn o.val.2 Ψ→ Signs H o.val.1 (Ψ ∘ gyrate I (V x)) K→ Allows k (Ψ ∘ V) x (v*K)
abbrev θ(B:ℝ)(n:ℕ) := (n+1:ℝ)*B
local notation "t₀"=> R.p.threshold
section lit
variable{z:E} {D v c D' σ fV tV:ℝ}{X Y:Support (More m)}(h: R.p.order=k) (p:paperT q k C D)(g:WrapG k σ D' v)(H:R.p.threshold ≤ σ)
include p
lemma perskin{X:Support (More m)} (hr:X⊆ Y)(he:∀ i∈inspectD Y, Tender (fun y=>faceValue (U_ y) i) z (C*t₀) k):
 let ξ':=fun u=> guardB S x R (M_ u) T q d l X; Allows k ξ' z (Cloak.priceK k (inspectD Y).card D) ∧ (z∈tsupport ξ' → warmY S R M X → pingS t₀ X (U_ z)):=by
 intro ξ'; have hv:inspectD X ⊆ inspectD Y:=fun i p=>mem_filter.mpr ⟨mem_univ _,fun h=> (mem_filter.mp p).2 (h.mono_left hr)⟩
 let V:= inspectD X \ M.key.costs; have hp: V ⊆ inspectD Y:=(show _ from sdiff_subset).trans hv; obtain ⟨c,m⟩:=p U_ (inspectD Y) V t₀ R.p.threshold_pos hp fun i x=>he _ (hp x); refine ⟨c,fun j ht i l'=>?_⟩ -- tune
 have hx : i∈ inspectD X:=mem_filter.mpr (show i∈(univ:Finset _)∧¬Disjoint X (touched i) from ⟨mem_univ _,l'⟩) -- inference fix
 by_cases v:i∈ M.key.costs
 · change Pressure.toll (U_ z) i < t₀; rw [show Pressure.toll _ _=_ from (pageB (M_ z) T x q d l R.beta i v)]; exact ht i v hx
 exact m j i (mem_sdiff.mpr ⟨hx,v⟩)
lemma acres(z:E) [FiniteDimensional ℝ E]{Y':E→ Cipher m}(w:Support (More m))(V:Support (More m))(hv:w⊆V)(B:Raid (LeanV (Single m)))(K:E→ Cipher m)(ht:∀ i∈inspectD V,Tender (fun y=>faceValue (U_ y) i) z (C*t₀) k)(hm: Y'=fun u=> if warmY S R M w then guardB S x R (M_ u) T q d l w • K u else 0)(hs:pingS t₀ w (U_ z)→ Rigid K k z B)(hb:0≤B): Rigid Y' k z (ξ k (Cloak.priceK k (inspectD V).card D) • B):=by
 let V'(u):=guardB S x R (M_ u) T q d l w; obtain ⟨m,h⟩:= perskin x T q d l R M F p hv ht; let b:= Cloak.priceK k (inspectD V).card D; have hg:0 ≤ ξ k b • B:=fun i=>mul_nonneg (show 0 ≤ ξ k b from by have ht :0≤b:=m.nonneg; unfold ξ; positivity) (hb i)
 by_cases l':warmY S R M w; swap; · apply zero_s _ hg; filter_upwards with u; simp only [hm,if_neg l']
 rw [hm]; simp_rw [if_pos l']; by_cases ht:z∈ tsupport V'; exact pace_p (hs (h ht l')) m
 apply zero_s _ hg; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with u p; simp only [show guardB _ _ _ _ _ _ _ _ _=0 from p,zero_smul]
include h H g
lemma porch(z:E) [FiniteDimensional ℝ E](X:Roc m) (ι:Raid (LeanV (Single m))) (hh: PressB R.p X.1 (if X.2 then R.F X.1 else R.slip X.1) fV tV) (u:∀ U,BedP R.p U (if X.2 then R.F X.1 else R.slip X.1) X.1 ι)
 (hv:0≤v)(hι:0≤ι)(he:∀ i∈inspectD X.1.val.2,Tender (fun y=> faceValue (U_ y) i) z (C*t₀) k)(hc:∀ i:Bond (More m),Skye.ends i⊆ X.1.val.2→ Tender (fun y=> U_ y i) z (D'*t₀) k):
 Rigid (fun y=>sheer S x R (M_ y) T q d l X) k z (Rue.ξ k (Cloak.priceK k (inspectD X.1.val.2).card D) • saber (θ v k • ι) 1) :=by
 let W:=X.1; let D':= if X.2 then R.F W else R.slip W; let Q(t):=D' (U_ t); have ht:0≤ θ v k • ι:=fun i=> mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤ k+1) hv) (hι i)
 refine acres x T q d l R M F p z (X.1.val.2) _ (Subset.refl _) _ (fun z=>exp (Q z)-1) he ?_ ?_ ((saber_r 1 ht (fun _=>1) showK).1) -- tune unused argument
 · funext i; by_cases z:X.2=true <;> simp only [sheer,Q,W,D',z,hallU,warmY,chillB] <;> rfl
 intro hz; apply wiser; refine ⟨Eventually.of_forall (fun x=>(fineShape _).allP),fun i=>?_ ⟩; let L(V:Pane m):=crumb (D' V).val i; let H':= U_ z; have hm :=u (U_ z) hz i; rw [show (fun t:tangD m=> L (increment H' t))=L ∘ gyrate univ H' from ?_] at hm -- maybe fails
 swap; · funext v; refine congrArg L ?_; unfold gyrate Function.comp increment; funext j; rw [steadyB,if_pos (mem_univ _)]
 rw [Pi.smul_apply, θ,smul_eq_mul,mul_assoc]; exact bare_p _ _ (g X.1 h H _ U_ z univ hc (fun i _ p=> (p (mem_univ _)).elim) L (ι i) (fun U V p=>congrArg (fun z:Cipher m=> crumb z.val i) (hh.term U V p)) hm)
lemma fortP (z:E) [FiniteDimensional ℝ E](X:Force m)(τ:Ids m)(ι:Raid (LeanV (Single m))) (hh: ForceB R.p X (R.K X) fV tV) (u:∀ U τ,pingS t₀ (X.val.1.val.2\X.val.2) U→∀ i:Finset (LeanV (Single m)),Signs R.p X.val.1.val.1 (fun t=> crumb (R.K X (increment U (openG R.p X.val.2 t),τ)).val i) (ι i))
 (hv:0≤v)(hι:0≤ι)(hs: X.val.2 ⊆ brushK M.key (chillB M) t₀)(hy:5*R.p.B+4 ≤ 10*radiusB x)(he:∀ i∈ inspectD X.val.1.val.2, Tender (fun y=> faceValue (U_ y) i) z (C*t₀) k)(hc:∀ i:Bond (More m),Skye.ends i⊆ X.val.1.val.2 → Tender (fun y=> U_ y i) z (D'*t₀) k):
 Rigid (fun y=>shineK S x R (M_ y) τ T q d l X) k z (Rue.ξ k (Cloak.priceK k (inspectD X.val.1.val.2).card D) • (θ v k • ι)):=by
 let Q(t):= R.K X (U_ t,τ); let B:= X.val.1; let P:=R.p; let Y:= X.val.2; have hx: 0 ≤ θ v k • ι:= fun i=> mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤ k+1) hv) (hι i)
 refine acres x T q d l R M F p z _ _ (sdiff_subset (s:= X.val.1.val.2) (t:=Y)) _ Q he rfl (fun hz=>?_ ) hx
 refine ⟨Eventually.of_forall (fun x=>(fineShape _).allP),fun i=>?_⟩; let L(V:Pane m):=crumb (R.K X (V,τ)).val i; let t:= unrest Y P.B; let H':= U_ z
 have hp:= u (U_ z) τ hz i; simp_rw [padP] at hp
 rw [Pi.smul_apply,θ,smul_eq_mul,mul_assoc]; exact bare_p _ _ (g B h H _ U_ z t hc (fun i _ v=> Eventually.of_forall fun y=> poignant_hold x T q d R.beta l M F Y hy hs i v y z) L (ι i) (fun V U k=>congrArg (fun z:Cipher _=> crumb z.val i) (hh.values _ _ _ _ k (fun _ _=>rfl))) hp)
end lit
end YM.CF.Rue
