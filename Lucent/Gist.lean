import YM.SU5.Thin.Avalanche.Shelter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter MeasureTheory ProbabilityTheory
open Regis.Resonance
open scoped Topology
namespace Gist

variable {I J:Type*} (f:I→I→ℂ)
/-- Manual Wick solver, independent of covariance PSD or even symmetry -/
def nib (g:List I→ℂ) (x:I)(a b:List I) :ℂ:=
 match b with
 | [] => 0
 | y::b=> f x y*g (a++b)+nib g x (a++[y]) b
def fuel (n:ℕ) (b:List I) :ℂ:=
 match n,b with
 | _,[]=>1
 | 0,_:: _=>0
 | n+1,x::b=>nib f (fuel n) x [] b
def vell (b:List I):ℂ:=fuel f b.length b

lemma fuels (n m:ℕ) (b:List I)(h:b.length ≤ n)(t:b.length≤ m): fuel f n b=fuel f m b:=by
 induction n generalizing m b with
 | zero=>cases b <;>cases m <;>simp_all [fuel]
 | succ n ih=>
  cases b with
  | nil=>cases m <;>rfl
  | cons x b=>
   cases m with
   | zero=>simp at t
   | succ m=>
    rw [fuel,fuel]
    suffices ∀ a c:List I,(x::(a++c)).length ≤ n+1→(x::(a++c)).length ≤ m+1→nib f (fuel f n) x a c=nib f (fuel f m) x a c from this [] b h t

    intro a c; induction c generalizing a with
    | nil=> simp [nib]
    | cons y c u=>
                   intro h t; rw [nib,nib]; congr 1
                   · rw [ih m _ (by simp at *; omega) (by simp at *; omega)]
                   apply u <;>simp at * <;>omega
lemma vell_nil: vell f []=1:=rfl
lemma vell_cons(x:I)(b:List I): vell f (x::b)=nib f (vell f) x [] b:=by
 rw [vell,List.length_cons,fuel]
 generalize h:b.length=n
 suffices ∀ a c:List I,(a++c).length=n → nib f (fuel f n) x a c=nib f (vell f) x a c from this [] b h
 intro a c; induction c generalizing a with
 | nil=>simp [nib]
 | cons y c u=>
   intro h; rw [nib,nib,vell,fuels f n ((a++c).length) (a++c) (by simp at *; omega) le_rfl]
   rw [u _ (by simp [←h])]

/- evaluating even the possibly divergent valuations off the distinct layout inside bins
    `memo` pays `vell`. -/
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
lemma vellWick (φ:I→E)(h:∀ x y, (inner ℝ (φ x) (φ y) : ℝ)= f x y) (b:List I) : (memo (b.map φ):ℂ)= vell f b:=by
 suffices ∀ n,∀ l:List I,l.length ≤ n → (memo (l.map φ):ℂ)= vell f l from this _ b le_rfl
 intro n; induction n with
 | zero=> intro l; cases l <;>simp [memo,payday,vell_nil]
 | succ n ih=>
   intro l; cases l with
   | nil=>simp [memo,payday,vell_nil]
   | cons x l=>
     rw [List.map_cons,gramStein,vell_cons]
     suffices ∀ a c:List I,(x::(a++c)).length ≤ n+1→(roster (φ x) (a.map φ) (c.map φ):ℂ)=nib f (vell f) x a c from this [] l
     intro a c; induction c generalizing a with
     | nil=> simp [roster,nib]
     | cons y c u=>
        intro t; rw [List.map_cons,roster,nib,←List.map_append,
          show a.map φ++[φ y]=(a++[y]).map φ from by simp]
        push_cast; rw [u _ (by simp_all only [List.length_append,List.length_cons,List.length_nil]; omega),h,ih _ (by simp_all only [List.length_append,List.length_cons,List.length_nil]; omega)]

-- pair sorting
lemma vellTendsto {J:Type*}{l:Filter J}(g:J→I→I→ℂ) (b:List I)
    (h:b.Pairwise (fun x y=> Tendsto (fun t=>g t x y) l (𝓝 (f x y)) )):
    Tendsto (fun t=> vell (g t) b) l (𝓝 (vell f b)):= by
 change Tendsto (fun t=> fuel (g t) b.length b) l (𝓝 (fuel f b.length b))
 generalize b.length=n
 induction n generalizing b with
 | zero=>exact tendsto_const_nhds (x:= fuel f 0 b) |>.congr' (by filter_upwards with t; cases b <;>simp [fuel])
 | succ n ih=>
   cases b with
   | nil=>exact tendsto_const_nhds
   | cons x b=>
     suffices ∀ a c, (x::(a++c)).Pairwise (fun x y=> Tendsto (fun t=>g t x y) l (𝓝 (f x y))) →
          Tendsto (fun t=> nib (g t) (fuel (g t) n) x a c) l (𝓝 (nib f (fuel f n) x a c)) from this [] b h
     intro a c; induction c generalizing a with
     | nil=> intro; exact tendsto_const_nhds
     | cons y c u=>
        intro orig; have e:=orig; simp_rw [List.pairwise_cons,List.pairwise_append,List.pairwise_cons] at e
        obtain ⟨hc,d,⟨p,t⟩,z⟩:= e
        have hz:= ih (a++c) (List.pairwise_append.mpr ⟨d,t,fun k w i u=>z k w i (List.mem_cons_of_mem y u)⟩)

        simp_rw [nib]
        exact ((hc y (List.mem_append_right a List.mem_cons_self)).mul hz).add (u (a++[y]) (by simpa using orig))

lemma vellMap (φ:J→I)(g:J→J→ℂ) (h:∀ x y,f (φ x) (φ y)=g x y) (l:List J): vell f (l.map φ)=vell g l:= by
 unfold vell; rw [List.length_map]
 generalize l.length=n
 induction n generalizing l with
 | zero=>cases l <;>simp [fuel]
 | succ n ih=>
   cases l with
   | nil=>rfl
   | cons x l=>rw [List.map_cons,fuel,fuel]
               suffices ∀ a b:List J, nib f (fuel f n) (φ x) (a.map φ) (b.map φ)=nib g (fuel g n) x a b from this [] l
               intro a b; induction b generalizing a with
               | nil=>simp [nib]
               | cons y b u=>rw [List.map_cons,nib,nib,h,←List.map_append,ih,show a.map φ++[φ y]=(a++[y]).map φ from by simp, u]
lemma only_nil {x:I}(t:List I)(h:∀ y∈t, f x y=0) (a:List I) : nib f (vell f) x a t=0:= by
 induction t generalizing a with|nil=>rfl|cons y t ih=>simp [nib,h y List.mem_cons_self,ih (fun i u=>h i (List.mem_cons_of_mem _ u))]

lemma vellDivide (s t:List I)(h:∀ x∈s,∀ y∈t, f x y=0):
    vell f (s++t)=vell f s * vell f t:=by
 revert h; suffices ∀ n,∀ s:List I,s.length≤n→(∀ x∈s,∀ y∈t, f x y=0)→ vell f (s++t)=vell f s * vell f t from this _ _ le_rfl
 intro n; induction n with
 | zero=>intro s; cases s <;>simp [vell_nil]
 | succ n ih=>
   intro s; cases s with
   | nil=>simp [vell_nil]
   | cons x s=>
     rw [List.cons_append,vell_cons,vell_cons]
     suffices ∀ a b:List I,(x::(a++b)).length ≤ n+1 →(∀ u∈(x::(a++b)),∀ v∈t, f u v=0) →
        nib f (vell f) x a (b++t)=nib f (vell f) x a b * vell f t from this [] s
     intro a b; induction b generalizing a with
     | nil=> intro _ h; rw [List.nil_append,only_nil _ _ (h _ List.mem_cons_self),nib,zero_mul]
     | cons y b u=>
        intro e l
        rw [List.cons_append,nib,nib,add_mul,mul_assoc]
        rw [u _ _ (by simpa using l),←List.append_assoc,ih _ _ (by intro i p; exact l i (by simp at *; grind))]
        all_goals simp at *; omega

lemma vellScale (u:ℂ)(b:List I) : vell (fun s t=> u^2*f s t) b = u^b.length * vell f b:= by
 let g:=fun s t=>u^2*f s t
 suffices ∀ n,∀ b:List I, fuel g n b=u^b.length * fuel f n b from this b.length b
 intro n; induction n with
 | zero=>intro b; cases b <;> simp [fuel]
 | succ n ih=>
   intro b; cases b with
   | nil=>simp [fuel]
   | cons x b=>
     rw [fuel,fuel]
     suffices ∀ a c:List I, nib g (fuel g n) x a c=u^((x::(a++c)).length)*nib f (fuel f n) x a c from this [] b
     intro a c; induction c generalizing a with
     | nil=>simp [nib]
     | cons y c p=>
        rw [nib,nib,p,ih,mul_add]; simp only [List.append_assoc,List.singleton_append]; rw [show (x::(a++(y::c))).length=2+(a++c).length from by simp; omega,pow_add]; unfold g; ring
