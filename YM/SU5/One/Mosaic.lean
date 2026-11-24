import YM.SU5.One.Glint
import YM.SU5.One.RibbonLens

/-!
# Mosaic: joint resolution on BOTH parity suites, no new pricing beyond Coherent/V
PairLens plan. Does thin both vol and UV *together* along that very path.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 160000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry Tapestry.Altitude
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s:ℕ)
variable {D: ℕ→ Family (tent Y H) → Family (tent Y H)}{n m:ℕ→ℕ}(d: Coherent Y H (i:=i) (k:=k) (E:=E) D n m)
local notation "K"=>tent Y H
local notation "𝒮"=> wingspan Λ l
local notation "ι"=> i ∘ n
local notation "σ"=> k ∘ m

section
-- Norming pointwise valuation with disjoint supports. Choice of free gauge world at fixed roomy host.
variable (S:Finset Cover)(b:Bool)
abbrev Dots := Squad S b × PairsC
def dust (x:Dots S b) : Bazaar S b →ₗ[ℂ] ℂ:=
 (LinearMap.proj x.2).comp ((daubL S).comp (LinearMap.proj x.1))
lemma normed_dust : Pique.Norming (F:=Bazaar S b) (dust S b):=
 ⟨fun x f=> (daubLe S (f x.1) x.2).trans (norm_le_pi_norm ..),fun r h=> bazaarLe S b _ r (fun i t=> h (i,t))⟩

lemma basePair (g:Axis)(z:ℤ)(f t:Bazaar S b):
 let X:= fresco S b K f * chime K g z (fresco S b K t)
 InTest K true (S∪ address g z S) false X ∧ pay X ((Tapestry.splay S b*‖f‖)*(Tapestry.splay S b*‖t‖)):=by
 intro X
 refine ⟨?_,pay_mul (frescoLe S b K · f ·) (chime_pay _ _ _ _ (F:=fresco S b K t) (frescoLe S b K · t ·))⟩
 simpa only [Bool.xor_self] using ((plaid S b K f).mono subset_union_left).mul ((flow_port K g z (plaid S b K t)).mono subset_union_right)

set_option maxHeartbeats 480000 in
private lemma delicate (R : Finset Cover)(g:Axis)(z:ℤ)(A:ℕ→Bazaar S b →ₗ[ℂ] Bazaar R b) (J : Calibration) :
 let T:=address g z R
 let W(j:ℕ)(f:Bazaar S b):Bazaar T b:= tess b R J (A j f) g z
 (∃ ℓ:Dots R b→Dots T b→ Bazaar S b→Bazaar S b→ℂ,
  (∀ ε:ℝ,0<ε→∀ᶠ j in atTop, ∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤1 → ‖dust R b w (A j f)*dust T b w' (W j f')-ℓ w w' f f'‖ ≤ ε) ∧
    ∃ c:ℝ,∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤ 1 → ‖ℓ w w' f f'‖≤c) →
    (∀ᶠ u:ℕ in atTop, (Pique.includeContinuous (E:=Bazaar S b) (F:=Bazaar R b) (A u)).toLinearMap=A u) ∧
    ∃ x:ℕ→ℕ, StrictMono x ∧ ∃ F, Tendsto (fun u=> Pique.includeContinuous (E:=Bazaar S b) (F:=Bazaar R b) (A (x u))) atTop (𝓝 F):= by
 rintro T W ⟨ℓ,hg,bB⟩; let κ:=Tapestry.splay T b+1
 have κ':0<κ:=by unfold κ Tapestry.splay; positivity
 have t:Tapestry.splay T b ≤ κ:=le_add_of_nonneg_right zero_le_one
 have c':∀ j f, ‖A j f‖≤κ*‖W j f‖:= fun j f=>(tess_n b R J g z (A j f)).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))
 obtain ⟨_,_,w⟩:= @Pique.fallsIn (Bazaar S b) (Bazaar R b) (Bazaar T b) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (Dots R b) (Dots T b) (dust R b) (dust T b) (normed_dust R b) (normed_dust T b) A W κ κ' c' ℓ hg bB
 refine ⟨?_,?_⟩
 · exact w.mono fun i w=>w.1
 exact @Pique.resolution (Bazaar S b) (Bazaar R b) (Bazaar T b) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (Dots R b) (Dots T b) (dust R b) (dust T b) (normed_dust R b) (normed_dust T b) A W κ κ' c' (Tapestry.splay R b) (by unfold Tapestry.splay; positivity) (fun i f=> tess_c b R J g z (A i f)) ℓ hg bB inferInstance

include V d
private lemma incision (α:ℕ→ℕ)(h:Tendsto α atTop atTop)(g:Axis)(z:ℤ)(e1:relativeApart S (address g z S) (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))) :
 let R:= 𝒮 S; let y:= (Λ.R.L.val:ℤ)*z; let T:= address g y R; let Z:= S∪ address g z S
 let t:=ι ∘ α; let v:=σ ∘ α; let A(j:ℕ):= reel Y H s b S (t j) (v j)
 let W(j:ℕ)(f:Bazaar S b):Bazaar T b:= tess b R K (A j f) g y
 let F(f t:Bazaar S b):= fresco S b K f * chime K g z (fresco S b K t)

 ∀ᶠ r in atTop, ∀ f f': Bazaar S b,Tower.block Y H s (t r) (v r) Z (F f f')=fresco R b K (A r f)* fresco T b K (W r f'):=by
 intro R y T Z t v A W F; let U:= 𝒮 Z
 -- purchase calls; equality in Family *for all periods* not only native
 have j1:Tendsto t atTop atTop:= (V.pick.grow_i.comp d.growsA).tendsto_atTop.comp h
 have q1:∀ᶠ r' in atTop,Satin.PairIdx Y s (t r') (v r'):= (h.eventually (d.finance (s+1))).mono fun j h' => ⟨h'.depth,h'.enters⟩

 filter_upwards [q1,j1.eventually (roomyTail Y H (s+1) R),j1.eventually (turning Y H (s+1) U), j1.eventually (roomyTail Y H (s+1) (U ∪ (R∪T))),j1.eventually (farEnough Y H S (address g z S) s e1)] with j a x a' u l'
 intro f f'; have h0 : InTest K true (R∪T) false (fresco R b K (A j f)* fresco T b K (W j f')):=by simpa only [Bool.xor_self] using ((plaid R b K (A j f)).mono subset_union_left).mul ((plaid T b K (W j f')).mono subset_union_right)
 apply exhibit_inj Y H (s+1) false (U ∪ (R∪T)) (t j) ((booked Y H s (t j) _ Z _).mono subset_union_left) (h0.mono subset_union_right) (Roomy.seats u)
 unfold F; rw [←tess_r b S K g z f']; exact reeled_pair Y H s b S (t j) _ g z a x a' l' f f'
private lemma cleave (α:ℕ→ℕ)(h:Tendsto α atTop atTop)(g:Axis)(z:ℤ) (e1:relativeApart S (address g z S) (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))) (e2:Disjoint (𝒮 S) (address g (Λ.R.L.val*z) (𝒮 S))):
 let R:= 𝒮 S; let y:= (Λ.R.L.val:ℤ)*z; let T:= address g y R
 let t:=ι ∘ α; let v:=σ ∘ α; let A(j:ℕ):= reel Y H s b S (t j) (v j)
 let W(j:ℕ)(f:Bazaar S b):Bazaar T b:= tess b R K (A j f) g y

 ∃ ℓ:Dots R b→Dots T b→ Bazaar S b→Bazaar S b→ℂ,
  (∀ ε:ℝ,0<ε→∀ᶠ j in atTop, ∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤1 → ‖dust R b w (A j f)*dust T b w' (W j f')-ℓ w w' f f'‖ ≤ ε) ∧
    ∃ c:ℝ,∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤ 1 → ‖ℓ w w' f f'‖≤c:= by
 intro R y T t v A W; let Z:=S∪ address g z S
 obtain ⟨p,hp⟩:= (show ∀ᶠ p:Side in atTop, Hosp (R∪T) ((K).c p) from (separates (tent Y H) (R∪T)).mono fun p h=> ⟨h⟩).exists
 let M:=(K).c p; have hr: Hosp R M:=⟨hp.seat_.mono subset_union_left⟩
 have hs: Hosp T M:=⟨hp.seat_.mono subset_union_right⟩
 have hl:=noTrespass R T K p e2 hp
 let F(f t:Bazaar S b):= fresco S b K f * chime K g z (fresco S b K t)
 let φ(f:Dots R b)(g:Dots T b):= pierce R T b b K p hr hs hl f.1 g.1
 have v0(w:Dots R b)(w':Dots T b):∃ x:Fields M,∀ (f:Bazaar R b)(g:Bazaar T b),φ w w' ((fresco R b K f * fresco T b K g) p x)= dust R b w f * dust T b w' g:= both_cards R T b b K p hr hs hl w.2 w'.2 w.1 w'.1
 choose X X' using v0; let ℓ(w:Dots R b)(w':Dots T b)(f f':Bazaar S b):=φ w w' (D s (F f f') p (X w w'))
 have j0:∀ᶠ r in atTop, ∀ f f': Bazaar S b,Tower.block Y H s (t r) (v r) Z (F f f')=fresco R b K (A r f)* fresco T b K (W r f'):=incision Y H V s d S b α h g z e1
 obtain ⟨C,hC,buys⟩:= d.implements s Z
 let c:= Tapestry.splay S b+1; have hx:0<c:= by unfold c Tapestry.splay; positivity
 have hv(f t:Bazaar S b)(hy:‖f‖≤ 1)(hq:‖t‖≤ 1): pay (F f t) (c*c):=by
    intro i x; let χ(w:Bazaar S b):=Tapestry.splay S b*‖w‖
    have hw(a:Bazaar S b)(h:‖a‖ ≤ 1): χ a≤ c:= by unfold χ; exact (mul_le_of_le_one_right (show 0 ≤ Tapestry.splay S b by unfold Tapestry.splay; positivity) h).trans (le_add_of_nonneg_right zero_le_one)
    exact ((basePair Y H S b g z f t).2 _ _).trans (mul_le_mul (hw f hy) (hw t hq) (by unfold Tapestry.splay; positivity) hx.le)
 have U0:∀ ε:ℝ,0<ε→∀ᶠ j in atTop, ∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤1 → ‖dust R b w (A j f)*dust T b w' (W j f')-ℓ w w' f f'‖ ≤ ε:=by
    intro ε l'
    filter_upwards [j0,h.eventually (buys (ε/(c*c)) (by positivity))] with j e q
    intro w w' f f' μ ν
    unfold ℓ; rw [←X', ←map_sub, ← e]; apply (pierce_bound R T b b K p hr hs hl _ _ _).trans
    have he:= (q _ (basePair Y H S b g z f f').1 _ (hv f f' μ ν)).2.2.1 p (X w w')
    exact he.trans_eq (div_mul_cancel₀ ε (by positivity))
 have uB:∃ c:ℝ,∀ w w' f f', ‖f‖≤1 → ‖f'‖ ≤ 1 → ‖ℓ w w' f f'‖≤c:=by
    obtain ⟨j,q⟩:= (buys 1 zero_lt_one).exists
    exact ⟨C*(c*c),fun w w' f f' h0 h1=> (pierce_bound R T b b K p hr hs hl _ _ _).trans ((q _ (basePair Y H S b g z f f').1 _ (hv f f' h0 h1)).1 ..)⟩
 exact ⟨ℓ,U0,uB⟩
lemma suture (α:ℕ→ℕ)(h:Tendsto α atTop atTop):
    (∀ᶠ u in atTop, ((Pique.includeContinuous (E:=Bazaar S b) (F:=Bazaar (𝒮 S) b) (reel Y H s b S ((ι) (α u)) ((σ) (α u)))).toLinearMap=reel Y H s b S ((ι) (α u)) ((σ) (α u)))) ∧
    ∃ x:ℕ→ℕ, StrictMono x ∧ ∃ A, Tendsto (fun u=> Pique.includeContinuous (E:=Bazaar S b) (F:=Bazaar (𝒮 S) b) (reel Y H s b S ((ι) (α (x u))) ((σ) (α (x u))))) atTop (𝓝 A):=by
 let g:Axis:=0
 obtain ⟨z,e1,e2⟩:= slide_both (Λ:=Λ) (l:=l) S g
 let R:= 𝒮 S; let y:= (Λ.R.L.val:ℤ)*z; let T:= address g y R; let Z:= S∪ address g z S
 let t:=ι ∘ α; let v:=σ ∘ α; let A(j:ℕ):= reel Y H s b S (t j) (v j)
 let W(j:ℕ)(f:Bazaar S b):Bazaar T b:= tess b R K (A j f) g y

 exact delicate S b R g y A K (cleave Y H V s d S b α h g z e1 e2)
end

section
open Set
lemma pruneMany {I: Type*}[Nonempty I][Countable I]{T:I→Type*} [∀ i,TopologicalSpace (T i)](f:(i:I)→ℕ→T i)
  (h:∀ i,∀ n:ℕ→ℕ,StrictMono n→ ∃ k:ℕ→ℕ, StrictMono k∧∃ v:T i,Tendsto (fun r=> f i (n (k r))) atTop (𝓝 v)) :∃ k:ℕ→ℕ,StrictMono k∧ ∀ i,∃ v:T i, Tendsto (fun r=> f i (k r)) atTop (𝓝 v):=by
 obtain ⟨x₀,m⟩:= exists_surjective_nat I
 let R:= {f:ℕ→ℕ //StrictMono f}
 choose g p using fun (n:ℕ)(k:R)=>h (x₀ n) k.val k.property
 let r:ℕ→R:= fun x=> Nat.rec (motive:=fun _=>R) ⟨id,strictMono_id⟩ (fun i c=> ⟨c.val ∘ (g i c),c.property.comp (p i c).1⟩) x
 let z(n:ℕ):= (r n).val n
 have s:StrictMono z:= strictMono_nat_of_lt_succ (fun n=> (r n).property (show n<g n (r n) (n+1) from Nat.lt_succ_self _|>.trans_le ((p n (r n)).1.id_le _)))
 refine ⟨z,s,fun i=>?_⟩; obtain ⟨a,rfl⟩:= m i
 obtain ⟨v,t⟩:= (p a (r a)).2
 let K':= (r (a+1)).val
 have ht(x n:ℕ)(u:n≤ x): Set.range (r x).val⊆ Set.range (r n).val:=by induction x,u using Nat.le_induction with | base=> rfl | succ m u ih=> intro x h; obtain ⟨y,rfl⟩:=h; exact ih (Set.mem_range_self (g m (r m) y))
 refine ⟨v,tendsto_def.mpr fun A h=>?_⟩
 obtain ⟨u,D⟩:= eventually_atTop.1 (t.eventually (show ∀ᶠ x in 𝓝 v,x∈A from h))
 filter_upwards [eventually_ge_atTop (a+1), s.tendsto_atTop.eventually (eventually_ge_atTop (K' u))] with i g H'
 obtain ⟨x,v⟩:= ht _ _ g (Set.mem_range_self i)
 change f (x₀ a) (z i)∈ A; have hv:z i=K' x:=v.symm
 rw [hv] at H' ⊢; exact D x ((r (a+1)).property.le_iff_le.mp (show K' u ≤ K' x from H'))
end

section
local notation "𝐐" S:max b:max=> Bazaar S b →L[ℂ] Bazaar (wingspan Λ l S) b
-- raw coupons; clipping after CP estimate, only used under predicates.
noncomputable def offersB (u v:ℕ) (S:Finset Cover)(b:Bool) : Bazaar S b →L[ℂ] Bazaar (wingspan Λ l S) b:= Pique.includeContinuous (E:=Bazaar S b) (F:=Bazaar (𝒮 S) b) (reel Y H s b S u v)
abbrev Collection (Λ:Preparation)(l:ℕ):= ∀ (_:ℕ)(S:Finset Cover)(b:Bool),Bazaar S b →L[ℂ] Bazaar (wingspan Λ l S) b

structure AdmitsCollection (f g:ℕ→ℕ) (M:Collection Λ l): Prop where
 continuousTail (s:ℕ)(S:Finset Cover)(b:Bool): ∀ᶠ i in atTop, (offersB Y H s (f i) (g i) S b).toLinearMap=reel Y H s b S (f i) (g i)
 proceeds (s:ℕ)(S:Finset Cover)(b:Bool): Tendsto (fun i=>offersB Y H s (f i) (g i) S b) atTop (𝓝 (M s S b))

include V d
lemma attains : ∃ f:ℕ→ℕ, StrictMono f ∧ ∃ M:Collection Λ l, AdmitsCollection Y H ((i∘n)∘f) ((k∘m)∘f) M:=by
 let X:=ℕ × Finset Cover × Bool
 let Λ₀(x:X):= (Bazaar x.2.1 x.2.2→L[ℂ] Bazaar (𝒮 x.2.1) x.2.2)
 letI(x:X): TopologicalSpace (Λ₀ x):= inferInstanceAs <| TopologicalSpace (Bazaar x.2.1 x.2.2→L[ℂ] Bazaar (𝒮 x.2.1) x.2.2)
 obtain ⟨z,hz,u⟩:= pruneMany (T:=Λ₀) (fun (x:X) r=>offersB Y H x.1 ((ι) r) ((σ) r) x.2.1 x.2.2) (fun x _ h=> (suture Y H V _ d x.2.1 x.2.2 _ h.tendsto_atTop).2) -- order?
 exact ⟨z,hz,(fun s A b=> (u (s,A,b)).choose),⟨fun s A b=>(suture Y H V s d A b z hz.tendsto_atTop).1,fun s S b=>(u (s,S,b)).choose_spec⟩⟩
end
end YM.CF.Buffered.Afterglow.Tower.One
