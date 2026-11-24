import YM.SU5.FiniteGaugeData.Poin.Alman
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Function Filter Metric Complex MeasureTheory Set OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {n:ℕ}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(x y:H)
open Boundary Probe Fin
local notation "D"=>Bench S
local notation "F"=> D →ₗ[ℂ] D
local notation "K"=>Cache S
variable {n:ℕ}(G:Fin n→ H.Op)(ν:Fin n→ℕ)(J:Bin n H.Op)
abbrev Xpay (i j:Fin n):H.Op:= J i j * Cache S (ν i+ν j)
structure PaysL :Prop where
 comm : ∀ i j:Fin n,i<j→Commute (J i j) (saucer S)
local notation "J₀"=> Xpay S ν J
lemma ypay (p:PaysL S J)(i j:Fin n)(h:i<j): Commute (J₀ i j) (saucer S):= (p.comm i j h).mul_left ( (Commute.refl (saucer S)).pow_left _)
-- record spun operation from J via domain subtype. no proof arguments in many lemmas if pass X satisfying Capsule
abbrev workW (V:Bin n ((Bench S) →ₗ[ℂ] (Bench S))):Prop:= ∀ (i j:Fin n),i<j→∀ x:Bench S,(V i j x).val= J₀ i j x.val
def yoke (p:PaysL S J) (i j:Fin n): (Bench S→ₗ[ℂ]Bench S) := if t:i<j then park S (J₀ i j) (autumn S _ (ypay S ν J p i j t)) else LinearMap.id
lemma works_V (p:PaysL S J): workW S ν J (yoke S ν J p):=by intro i j t x; rw [yoke,dif_pos t]; rfl
variable (Ω:Bench S) (w:saucer S Ω.val=Ω.val)
-- library (outside Celer)
lemma keepO (x:H)(w:saucer S x=x)(m:ℕ):Cache S m x=x:=by induction m with | zero=> simp [Cache] | succ n ih=> rw [Cache,pow_succ']; exact (congrArg (saucer S) ih).trans w
lemma hallO (w:saucer S Ω.val=Ω.val)(m:ℕ): hall S m Ω=Ω.val:= cache_I S m ( (releases S m Ω).trans (keepO S Ω.val w m).symm)
def panels (g:Fin n→ Test4) (i:Fin n): (F):= ℑ S (G i) (g i) (ν i)
lemma cajole (p:PaysL S J)(i j:Fin n)(h:i<j)(V:Bin n F)(v:workW S ν J V)(x: Bench S): hall S (ν i) (V i j x) = J i j ( Cache S (ν j) x.val):=by
 apply cache_I S (ν i); rw [releases,v i j h]; let A:=J i j; let k:=ν i; let l:=ν j; change (J₀ i j) x.val = _; unfold Xpay; rw [cacheA]; exact DFunLike.congr_fun (show A* (K k * K l)= K k* (A*K l) from (by rw [← mul_assoc,( (p.comm i j h).pow_right k ).eq,mul_assoc])) x.val -- defeq
-- recursive Eq.Price
include w
lemma resume (n:ℕ) (G:Fin (n+1)→ H.Op)(ν:Fin (n+1)→ℕ)(g:Fin (n+1)→ Test4)
    (J:Bin (n+1) H.Op)(p:PaysL S J)(V:Bin (n+1) F)(v:workW S ν J V):
 Rail (fun i=> valise S (G i) (g i)) J Ω.val = Cache S (ν 0) (Rail (panels S G ν g) V Ω).val:=by
 induction n with
 | zero=>
    rw [Rail_step,Rail_step,s1P,s1P,mul_one,mul_one]; change valise S (G 0) (g 0) Ω.val=Cache S (ν 0) (ℑ S (G 0) (g 0) (ν 0) Ω).val; rw [native,hallO _ Ω w]
 | succ n ih=>
    rw [Rail_step _ J,Rail_step _ V,s1S,s1S]; let t:Fin (n+1+1):= (0:Fin (n+1)).succ; let G':= Fin.tail G; let ν':=Fin.tail ν; let g':=Fin.tail g; let M:=Rail (panels S G' ν' g') (rump V) Ω; let L:= Rail (fun i=>valise S (G' i) (g' i)) (rump J)
    have he:L Ω.val = K (ν t) M.val:= ih _ _ _ _ (by constructor; intro i j h; exact p.comm _ _ (Fin.succ_lt_succ_iff.mpr h)) (rump V) (fun i j h=>v _ _ (Fin.succ_lt_succ_iff.mpr h))
    change valise S (G 0) (g 0) (J 0 t (L Ω.val))= Cache S (ν 0) (ℑ S (G 0) (g 0) (ν 0) (V 0 t M)).val; rw [he,native,cajole S ν J p _ _ (Fin.succ_pos _) V v M]
-- W price Eq on all n, all sector.
local notation "Q"=> panels S G ν
variable (g:Fin n→Test4)
lemma crowned (p:PaysL S J)(V:Bin n F)(v:workW S ν J V): (∫ u:Points n, concert S Ω.val Ω.val G J g u) = inner ℂ Ω.val (Rail (Q g) V Ω).val :=by
 rw [orches]; cases n with
 | zero=>rfl
 | succ n=> rw [resume S Ω w n G ν g J p V v,←ContinuousLinearMap.adjoint_inner_left (K (ν 0)),show (K _).adjoint=(K (ν 0)) from (saucer_sym S).pow _,keepO S Ω.val w]
#print axioms crowned
omit w
variable (C:ℝ) (L:ℕ→ Bin n H.Op)(V:ℕ→ Bin n ((Bench S) →ₗ[ℂ] (Bench S))) (p:∀ i,PaysL S (L i))(v:∀ i,workW S ν (L i) (V i))
def Gesture (L:ℕ→ H.Op):Prop := ∃ C:ℝ, (∀ i, ‖L i‖ ≤ C)∧ ∀ x:H,Tendsto (fun i=>L i x) atTop (𝓝 x)
lemma vision (L:ℕ→H.Op)(p:Gesture L) (Y:ℕ→ H)(t:Tendsto Y atTop (𝓝 y)): Tendsto (fun i=>L i (Y i)) atTop (𝓝 y):=by
 obtain ⟨J,v,u⟩:=p; have h:Tendsto (fun i=> L i (Y i-y)) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=> norm_nonneg _) (fun i=> ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (v i) (norm_nonneg _))) (by simpa only [sub_self, norm_zero,mul_zero] using (t.sub_const y).norm.const_mul J))
 exact Tendsto.congr' (Eventually.of_forall (fun x=>by dsimp only; rw [map_sub,sub_add_cancel])) ((by simpa only [zero_add] using h.add (u y)) : Tendsto (fun i=> L i (Y i-y)+L i y) atTop (𝓝 y))
-- need Lean parse K:ℝ over notation. g constant
abbrev Omit (_ _ :Fin n): (Bench S)→ₗ[ℂ](Bench S):=1 -- canonical.S. last
structure Solution (L:ℕ→ Bin n H.Op):Prop where
 bought (i:ℕ): PaysL S (L i)
 convergence: ∀ i j:Fin n,i<j→ Gesture (fun k=> Xpay S ν (L k) i j)
variable (X: Bench S)(y':ℕ→ Bench S)
lemma pandal (J: H.Op)(V: (Bench S)→ₗ[ℂ](Bench S))(p:Commute J (saucer S))(e:∀ x: Bench S,(V x).val=J x.val): hall S n (V X)=J (hall S n X):=by
 apply cache_I S n; rw [releases,e,show K n (J (hall S n X))=J (K n (hall S n X)) from DFunLike.congr_fun (p.pow_right n).eq.symm (hall S n X),releases]
include v
lemma wayStep (t:pays_to S atTop y' X)(e:Solution S ν L)(i j:Fin n)(d:i<j): pays_to S atTop (fun k=> V k i j (y' k)) X:= by
 intro m; have hp(k:ℕ):= pandal (n:=m) S (y' k) (Xpay S ν (L k) i j) (V k i j) (ypay _ ν (L k) (e.bought k) i j d) (v k i j d); simp_rw [hp]; exact vision _ _ (e.convergence i j d) _ (t m)
lemma mown (e:Solution S ν L): pays_to S atTop (fun i=> Rail (Q g) (V i) Ω) (Rail (Q g) (Omit S) Ω) := by
 -- use Rail_base. proof order induction.fin rep tail.
 induction n with
 | zero=> exact fun _=>tendsto_const_nhds -- Ω constant
 | succ n ih=>
    let J:= panels S G ν g; let U:= Fin.tail J; let M:=Omit (n:=n+1) S
    let Q'(i):=rump (V i); let f:= fun i=> Rail U (Q' i) Ω; let u:=(Rail U (rump M)) Ω; have he:pays_to S atTop f u:= ih (Fin.tail G) (Fin.tail ν) (Fin.tail g) (fun i=> rump (L i)) Q' (fun i j k p x=> v i _ _ (Fin.succ_lt_succ_iff.mpr p) x) ⟨fun i=>⟨fun _ _ t=> (e.bought i).comm _ _ (Fin.succ_lt_succ_iff.mpr t)⟩,fun j k p=> e.convergence _ _ (Fin.succ_lt_succ_iff.mpr p)⟩
    have hp:pays_to S atTop (fun i=> s1 n (V i) (f i)) ((s1 n M) u):= by
       cases n with
       | zero=> simp only [s1P]; exact he
       | succ n=> simp_rw [s1S]; exact wayStep S ν L V v u f he e 0 _ (Fin.succ_pos _)
    simp_rw [Rail_step (n:=n)]; exact ℑLim₁ S _ _ _ _ atTop _ _ tendsto_const_nhds hp -- tune. simpl reduce.
#print axioms wayStep
#print axioms mown
local notation "W"=> Rail (Q g) (Omit S)
omit v in
lemma traverse (e:Solution S ν L)(w:saucer S Ω.val=Ω.val) : Tendsto (fun i:ℕ=>∫ x, concert S Ω.val Ω.val G (L i) g x) atTop (𝓝 (inner ℂ Ω.val ((Rail (Q g) (Omit S) Ω).val))) :=by
 let V:= fun i=> yoke S ν (L i) (e.bought i); have hv(i:ℕ):= crowned S G ν (L i) Ω w g (e.bought i) (V i) (works_V S ν (L i) (e.bought i)); simp_rw [hv]; exact tendsto_const_nhds.inner (tune_in S _ atTop _ (mown S G ν Ω g L V (fun i=>works_V S ν (L i) (e.bought i)) e))
#print axioms traverse
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
