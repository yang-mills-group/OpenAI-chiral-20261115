import GaugeFieldConstruction.Eloi
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option maxRecDepth 1300
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One
open Lattice CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
def fitsK {β:Type}(i:Cover × β)(d:ℕ):Prop:= i.1∈cartO 0 d
theorem takesK {β:Type}[Fintype β](d:ℕ):∃ S:Finset (Cover×β),∀ x:Cover × β,fitsK x d→x∈S:= ⟨cartO 0 d×ˢ Finset.univ,fun x h=> Finset.mem_product.mpr ⟨h,mem_univ _⟩⟩
-- stop reducibility explosion for 4-cube
def grabG:Finset Wα:= Classical.choose (takesK 26)
def grabF:Finset Wφ:= Classical.choose (takesK 26)
lemma upG (i:Wα)(p:fitsK i 26):i∈ grabG:= Classical.choose_spec (takesK 26) i p
lemma upF (i:Wφ)(p:fitsK i 26):i∈ grabF:= Classical.choose_spec (takesK 26) i p
lemma prod_mem {A B:Type}(X:Finset A)(Y:Finset B)(x:A×B)(h:x.1∈X)(p:x.2∈Y): x∈X×ˢ Y:=Finset.mem_product.mpr ⟨h,p⟩
lemma cardBoundK {A B:Type}[Fintype A](S:Finset B)(f:A→B)(p:Injective f)(h:∀ x,f x∈S):Fintype.card A ≤ Fintype.card ↥S:= Fintype.card_le_of_injective (fun x=> (⟨f x,h x⟩:↥S)) (fun _ _ hv=>p (congrArg Subtype.val hv))
lemma forkG {N:Side}(x:Cover)(p:StampSet N x): zG x (Wasp N x p)∈ grabG:=by
 have h: LiftSeat (cT:=N) x p∈ cartO x 24:= (prospect_R ..).2 (seat_e x _)
 apply upG; unfold fitsK; rw [cart_spec (0:Cover) 26]; intro j
 change (LiftSeat (cT:=N) x p j-x j-0).natAbs ≤ 26; rw [sub_zero]; exact (((cart_spec ..).1 h j).trans (show 24≤26 from by decide))
lemma forkF {x:Cover}(p:ArcK x): zF x (Wry x p)∈grabF:= by
 apply upF; unfold fitsK; rw [cart_spec (0:Cover) 26]; intro i; have hp: nodeC p.1.val ∈ cartO x 24:=(ridge_spec _).mp p.1.property; have h:=(cart_spec ..).1 hp i; change ((2*p.1.val i-x i)-0).natAbs ≤ 26; simp [nodeC] at h; omega -- tune
lemma wG_in (x:Cover)(N:Side): Injective (zG x∘ Wasp N x):=by
 intro ⟨⟨i,H⟩,u⟩ ⟨⟨j,G⟩,t⟩ h; have he: (zG x (Wasp N x (⟨⟨i,H⟩,u⟩)))=(zG x (Wasp N x (⟨⟨j,G⟩,t⟩))):=h
 have V:= congrArg Prod.fst he; change prospect x i.1-x=prospect x j.1-x at V; have V:=sub_left_injective V; have ht:i=j:= Prod.ext ((prospect_eta N x i.1).symm.trans ((congrArg _ V).trans (prospect_eta ..))) (congrArg Prod.fst (congrArg Prod.snd he)) -- tune
 have hx:u=t:= congr_arg Prod.snd (congr_arg Prod.snd he); subst_vars; rfl
lemma wF_in(x:Cover): Injective (zF x ∘ Wry x):=by
 intro i j p; refine Prod.ext (Subtype.ext ?_) (show i.2=j.2 from (by have hx:=congr_arg Prod.snd p; exact hx)); ext k; apply mul_left_cancel₀ (show (2:ℤ)≠0 by norm_num); have h: 2*i.1.val=2*j.1.val:=sub_left_injective (b:=x) (by have hv:=congrArg Prod.fst p; exact hv); exact congr_fun h k
lemma SZbound(N:Side)(U:Genre):∃ L:ℕ,∀ x:Cover,Fintype.card (ShapeZ N x U)≤ L:=by
 have he(x:Cover): Fintype.card (StampSet N x)≤ Fintype.card ↥grabG:=cardBoundK grabG (zG x ∘ Wasp N x) (wG_in x N) (forkG x)
 have hl(x:Cover): Fintype.card (ArcK x)≤ Fintype.card ↥grabF:=cardBoundK grabF (zF x ∘ Wry x) (wF_in x) (fun i=>forkF i)
 cases U with
 | gauge=> refine ⟨(Fintype.card ↥grabG)^(Fintype.card (Fin 2)),?_⟩; intro x; change Fintype.card (Shx N x) ≤_; rw [Fintype.card_congr (Equiv.refl (Shx N x)),Fintype.card_fun]; exact Nat.pow_le_pow_left (he x) _ -- tune abbrev
 | pure=> refine ⟨(Fintype.card ↥grabF * Fintype.card ↥grabF),?_⟩; intro x; change Fintype.card (ArcK x × ArcK x) ≤ _; rw [Fintype.card_prod]; exact Nat.mul_le_mul (hl x) (hl x)
 | mixed=> refine ⟨Fintype.card ↥grabF *(Fintype.card ↥grabF * Fintype.card ↥grabG),?_⟩; intro x; change Fintype.card (ArcK x × ArcK x × StampSet N x)≤_; rw [Fintype.card_prod (α:=ArcK x) (β:=ArcK x × StampSet N x), Fintype.card_prod (α:=ArcK x) (β:=StampSet N x)]; exact Nat.mul_le_mul (hl x) (Nat.mul_le_mul (hl x) (he x))
-- uniform estimator.Buy Size rational
lemma licensed {α:Type*}{S:Finset α}{p:ℝ→ℕ→α→Prop}(h:∀ s∈S,∃ C>0,∀ᶠ i:ℕ in atTop,p C i s)(f: ∀ᶠ i:ℕ in atTop,∀ s b c,b ≤ c→p b i s→ p c i s):∃ C>0,∀ᶠ i:ℕ in atTop,∀ s∈S,p C i s:=by
 classical
 induction S using Finset.induction_on with
 | empty=> exact ⟨1,by norm_num, Eventually.of_forall (by simp)⟩
 | @insert x s p' IH=>
    obtain ⟨C,H,v⟩:= IH fun i e=>h i (mem_insert_of_mem e)
    obtain ⟨D,P,w⟩:=h x (mem_insert_self ..)
    refine ⟨C+D,by positivity,?_⟩; filter_upwards [v,w,f] with j v w f; intro i h; rcases mem_insert.mp h with t|t; · subst i; exact f _ _ _ (by linarith) w
    exact f _ _ _ (by linarith) (v i t)
variable (X:E4)(x y:ℕ → Cover)(t:ℕ→ℝ)(w:Tendsto t atTop (𝓝 0))(v:∀ᶠ i:ℕ in atTop,0<t i)(g:Tendsto (fun i=> NaR (t i) (x i) (y i)) atTop (𝓝 X))(h:X≠0)
include w v g h
abbrev gT (t:ℝ)(x y:Wα):=κg x y/(t:ℂ)^4
abbrev fT (t:ℝ)(x y:Wφ):=κF x y/(t:ℂ)^3
local notation "Dζ" => fun k:ℕ=>NaR (t k) (x k) (y k)
lemma Gauken (m:ℕ): ∃ C>0,∀ᶠ k:ℕ in atTop,∀ i j:Wα,zG (x k) i∈grabG→ zG (y k) j∈grabG→ Rally C ((t k)^(m+1)) (gT (t k) i j) (port ge (Dζ k) (Gauke (x k) i m (t k)) (Gauke (y k) j m (t k))):=by
 let R(b)(k:ℕ)(z:Wα × Wα):Prop:=∀ i j:Wα,z=(zG (x k) i,zG (y k) j)→ Rally b ((t k)^(m+1)) (gT (t k) i j) (port ge (Dζ k) (Gauke (x k) i m (t k)) (Gauke (y k) j m (t k)))
 have hx(z:Wα × Wα):∃ C>0,∀ᶠ i:ℕ in atTop, R C i z:=by
    rcases z with ⟨z,y'⟩; obtain ⟨C,hp,P⟩:= tilted (Glint 0 z) (Glint 0 y') X Dζ t w g h lace ge (pinG z) (pinG y') baseG topG m v
    refine ⟨C,hp,?_⟩; filter_upwards [P,v] with k p X0; intro i j e; have Z:=Prod.mk.inj e; rw [Z.1,Z.2] at p; have hz:= p.2; have hv:=p.1; rw [←G_near,←G_near] at hz hv; unfold Gauke; rw [gT,G_put _ _ _ _ (NX X) (NXp _ h) (t k) X0 hv,mul_div_cancel_left₀ _ (show ((t k:ℂ)^4)≠0 from by exact pow_ne_zero _ (by exact_mod_cast X0.ne'))]; exact hz -- tune
 obtain ⟨C,H,Q⟩:=licensed (p:=R) (S:=grabG×ˢ grabG) (fun s _=> hx s) (v.mono fun i h b _ _ p g x y u=> (g x y u).mono p (by positivity))
 exact ⟨C,H,Q.mono (fun k h i j p hT=>h _ (prod_mem grabG grabG (zG (x k) i,zG (y k) j) p hT) i j rfl)⟩
lemma Thröken (m:ℕ): ∃ C>0,∀ᶠ k:ℕ in atTop,∀ i j:Wφ,zF (x k) i∈grabF→ zF (y k) j∈grabF→ Rally C ((t k)^(m+1)) (fT (t k) i j) (port (yarn false) (Dζ k) (Freight (x k) i false m (t k)) (Freight (y k) j true m (t k))):=by
 let R(b)(k:ℕ)(z:Wφ × Wφ):Prop:=∀ i j:Wφ,z=(zF (x k) i,zF (y k) j)→ Rally b ((t k)^(m+1)) (fT (t k) i j) (port (yarn false) (Dζ k) (Freight (x k) i false m (t k)) (Freight (y k) j true m (t k)))
 have hx(z:Wφ × Wφ):∃ C>0,∀ᶠ i:ℕ in atTop, R C i z:=by
    rcases z with ⟨z,y'⟩; obtain ⟨C,hp,P⟩:= tilted (Garn z) (Garn y') X Dζ t w g h (stride false) (yarn false) (pinF z) (pinF y') (baseF false) (topF false) m v
    refine ⟨C,hp,?_⟩; filter_upwards [P,v] with k p X0; intro i j e; have Z:=Prod.mk.inj e; rw [Z.1,Z.2] at p; have hz:= p.2; have hv:=p.1; rw [←F_near,←F_near] at hz hv; unfold Freight; rw [fT,F_put _ _ _ _ (NX X) (NXp _ h) (t k) X0 hv,mul_div_cancel_left₀ _ (show ((t k:ℂ)^3)≠0 from by exact pow_ne_zero _ (by exact_mod_cast X0.ne'))]; exact hz -- tune
 obtain ⟨C,H,Q⟩:=licensed (p:=R) (S:=grabF×ˢ grabF) (fun s _=> hx s) (v.mono fun i h b _ _ p g x y u=> (g x y u).mono p (by positivity))
 exact ⟨C,H,Q.mono (fun k h i j p hT=>h _ (prod_mem grabF grabF (zF (x k) i,zF (y k) j) p hT) i j rfl)⟩
#print axioms Thröken
#print axioms Gauken
end YM.GaugeFieldConstruction.Wick.Yacht
end
