import YM.SU5.FiniteGaugeData.Tower.Upright
import YM.Hilbert.Kolmogorov
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Hilbert.Freight
open Function Filter UniformSpace Set Finset Analysis
open scoped Topology BigOperators InnerProductSpace ComplexOrder ComplexConjugate Classical
local notation "V" => ℂ
variable {S:Type}[AddCommGroup S][Module ℂ S]
structure Fleet (S:Type)[AddCommGroup S][Module ℂ S] where
 raise : ∀(s t:ℕ), s ≤ t → S →ₗ[ℂ] S
 cash : ∀(_ : ℕ), S →ₗ⋆[ℂ] S→ₗ[ℂ] ℂ
 pos : ∀ t (f:S),0 ≤ cash t f f
 spends : ∀{s t:ℕ}(h:s≤t)(f g:S),cash s f g=cash t (raise s t h f) (raise s t h g)
 seed : ∀ s (x:S), raise s s le_rfl x=x
 joint : ∀{s t u:ℕ}(i:s≤t)(j:t≤u)(x:S),raise t u j (raise s t i x)=raise s u (i.trans j) x
namespace Fleet
variable (F : Fleet S)
local notation "ρ" i:max=> F.raise _ _ i
abbrev Aboard (S:Type):= ℕ × S
def worth (x y:Aboard S):ℂ:= F.cash (max x.1 y.1) ((ρ (le_max_left x.1 y.1)) x.2) ((ρ (le_max_right x.1 y.1)) y.2)
theorem payMore {x y:Aboard S}{z:ℕ}(a:x.1≤ z)(b:y.1≤ z): F.worth x y= F.cash z ((ρ a) x.2) ((ρ b) y.2):=by unfold worth; rw [F.spends (max_le a b),F.joint,F.joint]
theorem earns : NNKernel F.worth:=by
 intro n f; let k:= univ.sup (fun i=> (f i).1); have h(i):(f i).1 ≤ k:=Finset.le_sup (f:=fun i=>(f i).1) (Finset.mem_univ _) -- implicit binder problem
 simp_rw [F.payMore (h _) (h _)]; exact (_root_.YM.CF.Buffered.Afterglow.Tower.halfSpaceKernel (F.cash k) (F.pos k)) _
noncomputable def warrant: Kernel.Gram F.worth:=Classical.choice (Kernel.host (F.earns))
abbrev Room:= F.warrant.H
lemma room_ext {x y:F.Room} (p:∀s (v:S), inner ℂ x (F.warrant.plant (s,v))=inner ℂ y (F.warrant.plant (s,v))):x=y:=by
 apply ext_inner_right ℂ
 intro q; change (innerSL ℂ x) q=(innerSL ℂ y) q; exact DFunLike.congr_fun (F.warrant.by_bud fun i=> p i.1 i.2) q
local notation "c₀"=> F.warrant.plant
private lemma payIt {s t q:ℕ}(f g:S)(a:s≤q)(b:t≤q): inner ℂ (c₀ (s,f)) (c₀ (t,g))=F.cash q ((ρ a) f) ((ρ b) g):= (F.warrant.measure _ _).trans (F.payMore (x:=(s,f)) (y:=(t,g)) a b)
noncomputable def load (s:ℕ): S →ₗ[ℂ] F.Room where
 toFun f:= c₀ (s,f)
 map_add' x y:=by
    apply F.room_ext; intro t v; let u:= max s t; have h:s≤u:= le_max_left ..; have hx:t≤u:= le_max_right ..
    rw [inner_add_left, F.payIt _ _ h hx,F.payIt _ _ h hx,F.payIt _ _ h hx,map_add,map_add,LinearMap.add_apply]
 map_smul' p x:=by
    apply F.room_ext; intro t v; let u:= max s t; have h:s≤u:= le_max_left ..; have hx:t≤u:= le_max_right ..
    change inner ℂ (c₀ (s,p•x)) _=inner ℂ (p • _) _; rw [inner_smul_left,F.payIt _ _ h hx,F.payIt _ _ h hx,map_smul,map_smulₛₗ,LinearMap.smul_apply]; rfl
local notation "l"=> F.load
lemma pays {s t q:ℕ}(f g:S)(a:s≤q)(b:t≤q): inner ℂ (l s f) (l t g)=F.cash q ((ρ a) f) ((ρ b) g):=F.payIt _ _ a b
lemma paysHere (s:ℕ)(x y:S): inner ℂ (l s x) (l s y)= F.cash s x y:=by rw [F.pays _ _ (le_refl s) (le_refl s),F.seed,F.seed]
lemma rise {s t:ℕ}(i:s ≤ t)(p:S): l s p=l t ((ρ i) p):=by
 apply F.room_ext; intro y z; let u:=max y t; have a:y≤u:=le_max_left ..; have b:t≤u:=le_max_right ..
 change _=inner ℂ _ (l y z); rw [show c₀ (y,z)=l y z from rfl,F.pays _ _ (i.trans b) a,F.pays _ _ b a,F.joint]
lemma dense (s:ℕ) : Dense (⋃ i:ℕ,Set.range (l (i+s))):=by
 let f(i:ℕ):= LinearMap.range (l (i+s))
 have h:Monotone f:=by rintro i j p _ ⟨x,rfl⟩; exact ⟨(ρ (by omega:(i+s)≤(j+s))) x,(F.rise (by omega) x).symm⟩ -- isGE correction
 have he:(⋃ i:ℕ,Set.range (l (i+s)))= ↑(⨆ i,f i):=Eq.symm (Submodule.coe_iSup_of_directed f h.directed_le)
 rw [he]; refine F.warrant.dense.mono (Submodule.span_le.mpr ?_); rintro _ ⟨i,rfl⟩
 let t:= i.1; let b':t≤t+s:=by omega
 exact (le_iSup f i.1) (show c₀ i∈f i.1 from ⟨(ρ b') i.2,(F.rise b' i.2).symm⟩)

-- create bounded operator from all reports at sufficiently high levels
variable {T:Type*}[NormedAddCommGroup T][NormedSpace ℂ T][CompleteSpace T]
variable (s:ℕ) (p:∀ t≥s,S→ₗ[ℂ] T)
variable (Q:∀{t u:ℕ}(i:s≤t)(j:t≤u)(x:S), p u (le_trans i j) ((F.raise _ _ j) x)=p t i x)
local notation "Φ"=> p
include Q
lemma bound (C:ℝ) (h:0 ≤ C)(v:∀ t (u:s≤t)(x:S), ‖Φ t u x‖≤ C * ‖F.load t x‖): ∃ A:F.Room →L[ℂ] T, ‖A‖≤C ∧∀ i (u:s ≤ i)(x:S), A (l i x)=p i u x:=by
 let X:=Aboard S
 let Ψ(x:X):= p (max s x.1) (le_max_left ..) ((ρ (le_max_right s x.1)) x.2)
 have hΨ(x:X){a:ℕ}(g:s≤a)(b:x.1 ≤ a):Ψ x=p a g ((ρ b) x.2):=by
    unfold Ψ; rw [← Q _ (max_le g b), F.joint]
 let td:=Finsupp.linearCombination ℂ Ψ
 have ht(f:X→₀ ℂ): ∀ᶠ i in atTop,∃ (h:s ≤ i)(x:S),td f=p i h x ∧ F.warrant.stems f=l i x:=by
    induction f using Finsupp.induction_linear with
    | zero=> exact (eventually_ge_atTop s).mono fun i p=> ⟨p,0,by simp,by simp⟩
    | add f g u w=> filter_upwards [u,w] with i ⟨h,x,h₁,h₂⟩ ⟨_,y,e,f⟩; exact ⟨h,x+y,by rw [map_add,map_add,h₁,e],by rw [map_add,map_add,h₂,f]⟩
    | single k y=>
       filter_upwards [eventually_ge_atTop s,eventually_ge_atTop k.1] with i h v
       refine ⟨h,y • ((ρ v) k.2),?_,?_⟩
       · unfold td; rw [Finsupp.linearCombination_single,map_smul,hΨ k h v]
       unfold Kernel.Gram.stems; rw [Finsupp.linearCombination_single,map_smul,show F.warrant.plant k=l k.1 k.2 from rfl,F.rise v]
 obtain ⟨A,t,q⟩:= F.warrant.by_bound Ψ C h (fun f=>by
    obtain ⟨i,g,u,e,m⟩:= (ht f).exists; change ‖td f‖≤ _; rw [e,m]; exact v _ _ _)
 refine ⟨A,t, fun i u x=>?_⟩
 rw [show l i x=c₀ (i,x) from rfl,q,hΨ (i,x) u (show _ ≤ i from le_refl i)]; exact congrArg _ (F.seed ..)
omit Q
lemma limit_ext{C G:F.Room→L[ℂ] T}(h:∀ i,s ≤ i→∀ x:S, C (F.load i x)=G (F.load i x)):C=G:=by
 apply F.warrant.by_bud; intro q; change C (l q.1 q.2)=G (l _ q.2); rw [F.rise (le_max_left q.1 s)]; apply h; omega
-- both sides
end Fleet
end YM.Hilbert.Freight
#print axioms YM.Hilbert.Freight.Fleet.load
#print axioms YM.Hilbert.Freight.Fleet.bound
#print axioms YM.Hilbert.Freight.Fleet.dense
