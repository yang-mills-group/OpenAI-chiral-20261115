import YM.CF.Vp929.Law.Growth
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms March Filter
open scoped Topology Classical
namespace Delta

variable (χ:Cover→ℕ) (d C:Side) {x y:Cover}
local notation "Ӄ"=> (d.val*C.val)
abbrev lotto (m:ℕ):ℕ:= Ӄ+2*C.val*(m+1)
def plotLine(a:ℤ)(p:ℕ): Wall:= ⟨a-p,a+p,by omega⟩
def court(i:Cover)(p:ℕ):Rooms:=fun j=>plotLine (i j) p
protected lemma plot_here(p:ℕ)(x y:Cover) : here x ≤ court y p ↔ Range p y x:=by
 constructor <;> intro a i
 · obtain ⟨e,v⟩:=Wall.seen (a i); change y i - _≤ x i at e; change x i ≤ y i+_ at v; omega
 have t:=a i; exact ⟨show y i-↑p ≤ x i from by omega,show x i ≤ y i+↑p from by omega⟩
def toll (C:Side)(x y:Rooms): Prop:=∀ i:Axis, ∀ a b:ℤ, (x i).tips a → (y i).tips b → C.val ≤ (b-a).natAbs
lemma tollR {x y:Rooms}(v:toll C x y): toll C y x :=fun i a b h t=> by have h:= v i b a t h; omega
private lemma differ {m n:ℕ}(p:m<n):lotto d C m+2*C.val≤ lotto d C n:=by
 have h:m+1+1≤ n+1:=by omega
 let q:= Nat.mul_le_mul_left (2*C.val) h; unfold lotto; rw [Nat.mul_add ..] at q; omega
abbrev end0 (p:Wall)(b:Bool):ℤ:= if b then p.a else p.b
private lemma reach (A:Rooms)(i)(a b:Bool)(x:Cover){m n:ℕ} (t:(end0 (A i) a-end0 (court x (lotto d C m) i) b).natAbs < C.val)(v:(end0 (A i) a-end0 (court x (lotto d C n) i) b).natAbs < C.val):m=n:=by
 by_contra e; have H0:m<n∨n<m:=(by omega); obtain l|l:=H0; all_goals
    obtain k:= differ d C l
    cases a <;> cases b <;> simp only [end0,court,plotLine, ↓reduceIte,Bool.false_eq_true] at t v <;> omega
abbrev emits(o:Cover)(X:Cover→Rooms)(V:Set Cover)(L:ℕ):Prop:= (∀ y∈ V,Range (1000*(d.val*C.val)) o y→ toll C (X y) (court o (lotto d C L)))
private lemma window (z:64*(pinch+1)≤d.val) (o:Cover)(X:Cover → Rooms)(V:Set Cover)(u:sep Ӄ V):∃ n:ℕ, emits d C o X V n ∧ n < (16*pinch+1):=by
 classical
 obtain ⟨K,w,g⟩:= gas V o (d*C) u; by_contra! h
 have h'(s):s<16*pinch+1→∃ k∈ K,∃ i,∃ a b:Bool,(end0 (X k i) a-end0 (court o (lotto d C s) i) b).natAbs < C.val:=by
    intro e; have H: ¬ emits d C o X V s:= fun p=>e.not_ge (h s p); unfold emits toll at H; push Not at H; obtain ⟨k,v,l,i,a,b,u,t,p⟩:=H; refine ⟨k, (w.symm ▸ And.intro v l : k∈ (K:Set Cover)),i,?_⟩; cases u with
    | inl u=> cases t with | inl t=> exact ⟨true,true,by unfold end0; simp only [↓reduceIte,u,t]; omega⟩ | inr t=> exact ⟨true,false,by unfold end0; simp only [↓reduceIte,u,t,Bool.false_eq_true]; omega⟩
    | inr u=> cases t with | inl t=> exact ⟨false,true,by unfold end0; simp only [↓reduceIte,u,t,Bool.false_eq_true]; omega⟩ | inr t=> exact ⟨false,false,by unfold end0; simp only [↓reduceIte,u,t,Bool.false_eq_true]; omega⟩
 choose k W i a b E using fun s:Fin (16*pinch+1)=>h' s s.isLt
 let Y(s:Fin (16*pinch+1)): K × Axis × Bool × Bool:=(⟨k s,W s⟩,i s,a s,b s); have ht: Function.Injective Y:=by
    intro u v e; unfold Y at e; simp only [Prod.mk.injEq,Subtype.mk.injEq] at e; have p:= E u; rw [e.1,e.2.1,e.2.2.1,e.2.2.2] at p; exact Fin.ext (reach d C _ _ _ _ _ p (E _))
 obtain A:= Fintype.card_le_of_injective _ ht; rw [Fintype.card_fin] at A; simp only [Fintype.card_prod,Fintype.card_coe,Axis, Fintype.card_bool,Fintype.card_fin] at A; omega
lemma height(p:64*(pinch+1) ≤ d.val){n:ℕ}(hn:n<16*pinch+1): (d.val*C.val+1 ≤ lotto d C n)∧ lotto d C n ≤2*(d.val*C.val):=by
 unfold lotto; have h:0 < C.val:= C.property; constructor <;> nlinarith
abbrev Warmth(x:Cover):=∃ i:ℕ,cull χ Ӄ x∧ χ x=i
abbrev watch(o y:Cover):Prop:=cull χ Ӄ y∧ Range (1000*Ӄ) o y ∧ χ y < χ o
def ballot (o:Cover):ℕ:= sInf {i:ℕ | ∀ y:Cover, ∀ u:watch χ d C o y,toll C (court y (lotto d C (ballot y))) (court o (lotto d C i)) }
termination_by χ o
decreasing_by exact u.2.2
lemma culled (z:64*(pinch+1) ≤ d.val)(Q:Coloring χ (1000*Ӄ)) (x:Cover):let M:=ballot χ d C; let F(y):=court y (lotto d C (M y)); (∀ y:Cover,watch χ d C x y→ toll C (F y) (F x))∧ Ӄ+1 ≤ lotto d C (M x) ∧ lotto d C (M x) ≤2*Ӄ:=by
 intro M F; let Φ(i:ℕ):Prop:=∀ y:Cover, watch χ d C x y → toll C (F y) (court x (lotto d C i)); obtain ⟨n,v,u⟩:=window d C z x F {y|watch χ d C x y} (fun i (p:watch _ _ _ _ _) j (v:watch ..)=> firm χ Q (by omega) i p.1 j v.1); have t:Φ n:=fun y e=>v y e e.2.1; let A:Set ℕ:=Φ;
 have E:M x=sInf A:=by unfold M; rw [ballot]; rfl
 have e:M x∈A:= E.symm ▸ Nat.sInf_mem (show A.Nonempty from ⟨n,t⟩); exact ⟨e,height d C z (lt_of_le_of_lt (show M x ≤ n from E ▸ (Nat.sInf_le t : sInf A≤ n)) u)⟩

abbrev clusterQ(o:Cover):=court o (lotto d C (ballot χ d C o))
def windQ :Set Rooms:= clusterQ χ d C '' {x| cull χ Ӄ x}
lemma collation(z:64*(pinch+1) ≤ d.val)(Q:Coloring χ (1000*Ӄ)): Stiff (windQ χ d C) (100*(4*Ӄ)) C.val:=by
 let W(i:Cover):= ballot χ d C i; let V i:=lotto d C (W i);
 rintro x ⟨u,g,rfl⟩ y ⟨r,k,rfl⟩ v i a b ha hb; have hu:=culled χ d C z Q u; have hr:= culled χ d C z Q r; change _= _∨_ at ha hb
 have t(j): Range (V j) j ((court j (V j)).foot):= Delta.plot_here ..|>.1 (foot_in _)
 have hv:Range (1000*Ӄ) u r:= ((t u).trans (v.trans (t r).symm)).mono (by have u: V u≤ 2*Ӄ := hu.2.2; have h: V r≤2*Ӄ:=hr.2.2; omega)
 rcases lt_trichotomy (χ u) (χ r) with v|v|v; · exact Or.inr (hr.1 u ⟨g,hv.symm,v⟩ i a b ha hb)
 · have he:= Q u r hv v; subst r; have h:C.val ≤ Ӄ:= Nat.le_mul_of_pos_left _ d.property; have hc: Ӄ+1 ≤ V u:= hu.2.1; change u i - V u=a∨u i+ V u=a at ha; change u i- V u=b∨u i+ V u=b at hb; omega
 exact Or.inr (tollR C (hu.1 r ⟨k,hv,v⟩) _ _ _ ha hb)
end Delta
end YM.CF.VolumeCape
