import GaugeFieldConstruction.FruitCT
/-!
# S prices and purchases. Nested contour comparison from actual prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Finset Works_Nest
open scoped Topology BigOperators ContDiff
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] 

abbrev add (x : X) (v : Fin n→ X) : Fin (n+1)→ X:= Fin.cons x v
abbrev placard (X : Type*) := Axis → Axis → X
structure Palace (X : Type*) [AddCommGroup X] [Module ℂ X] where
  fee (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n=> X) (Bond n)
  rearr {n : ℕ} (s : Equiv.Perm (Fin n)) (x : Fin n→X) (p : Test n): fee n (x ∘ s) (perm s.symm p)=fee n x p -- check direction: x labels query on l, (x∘ s) query coord y=> S(x,y post s^-1), perm? perm s.symm p y=p(y∘s.symm), integral yes
namespace Palace
variable (S : Palace X)
variable {k : Fin n}

def spot (x : Fin n→X) (p : Fin n): X →ₗ[ℂ]Bond n := (S.fee n).toLinearMap x p
@[simp] lemma spot_cost (x : Fin n→X) (i) (g) : S.spot x i g=S.fee n (update x i g):=rfl

def tagged (x : Fin n→X): X →ₗ[ℂ] Bond (n+1) := S.spot (add 0 x) 0
@[simp] lemma tagged_cost (x : Fin n→X) (i) : S.tagged x i=S.fee _ (add i x):= by simp only [tagged,spot_cost,Fathom.add,Fin.update_cons_zero] -- check
lemma into (x : Fin n→X) (k) (t v : X): S.spot (add t x) k.succ v=S.tagged (update x k v) t:=by simp only [spot_cost,tagged_cost,Fathom.add,← Fin.cons_update] -- check k infer

def armed (J : placard X) (x : Fin n→ X): Variation n := fun i j=> S.tagged x (J i j)
abbrev Bills := ∀ n:ℕ, Fin n→Payroll n

def postage (i : Axis): Bills:= fun _ _=>ticket i
def rpm (Ω : Ortho.Skew) : Bills:=fun _ k=>desk k Ω

-- extends when inert extra point inserted before old externals

def rotor : Equiv.Perm (Fin (n+2)) := Equiv.swap 0 (0 : Fin (n+1)).succ
lemma rotor_inv : (rotor (n:=n)).symm=rotor := Equiv.symm_swap ..
lemma head' : (rotor (n:=n)) 0=Fin.succ 0:=Equiv.swap_apply_left ..
lemma true' : (rotor (n:=n)) (Fin.succ 0)=0:= Equiv.swap_apply_right ..
lemma external' (i:Fin n) : rotor i.succ.succ=i.succ.succ:= Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h=> Fin.succ_ne_zero i (Fin.succ_inj.mp h))
lemma on_labels (x : Fin n→X) (a b:X) : add a (add b x) ∘ rotor=add b (add a x):= funext fun i=>by
  refine Fin.cases ?_ (fun j=> ?_) i
  · simp [head',Fathom.add]
  refine Fin.cases ?_ (fun k=> ?_) j
  · simp only [true',Fathom.add,comp_apply,Fin.cons_zero,Fin.cons_succ]
  simp [external',Fathom.add]
lemma tops (x : Points (n+2)) : helm (rearrange rotor x)=helm (riders x) := by rw [helm_head,rearrange_at,head']; rfl
lemma hop (x : Points (n+2)) : helm (riders (rearrange rotor x))=helm x :=by
  change x (rotor (Fin.succ 0)) = _; rw [true']; rfl
lemma scrap (x : Points (n+2)) : riders (riders (rearrange rotor x))=riders (riders x):= PiLp.ext fun i=>by change x (rotor i.succ.succ) = _; rw [external']; rfl
lemma flank (x : Points (n+2)): rearrange rotor (rearrange rotor x)=x:= PiLp.ext fun i=> by rw [rearrange_at,rearrange_at, rotor,Equiv.swap_apply_self]

def Client (K : Bills): Prop:= ∀ n (q : Points (n+2)) (k : Fin n) i, (K _ k.succ).K i q= (K n k).K i (riders (rearrange rotor q))
lemma posted (a):Client (postage a) := fun _ _ _ _=> rfl
lemma tilted (Ω):Client (rpm Ω) := fun n q k i=> by
  change _ = (desk _ _).K _ _; change (desk _ _).K _ _=(desk _ _).K _ _
  rw [angle,angle]; have he := hop q; change riders (rearrange rotor q) 0=q 0 at he
  rw [he,scrap]; rfl

-- simple Ward insertion. F → Y.
def Reaches (J : placard X) (K : Bills) (V W:X): Prop := ∀ n (x : Fin n→X) (k : Fin n) (p : Test n) (b : Bulb) (v:Works b p k),
    S.spot x k W p=delta (K n k) p b v.cared (S.armed J (update x k V))
-- compare commuting
lemma shellflip (J T:placard X) (K L:Bills) {p : Test n} {a b} (i j m s) (x : Fin n→X) (k : Fin n)
    (c : Client K) (d:Client L) (g : Works b p k) (h : Works a p k) (w: Before b a) :
    S.armed T (add (J i j) x) m s (testcut (L _ k.succ) (testcut (K n k) p a h.cared i j) b (resident _ g h w i j).cared m s) =
      S.armed J (add (T m s) x) i j (testcut (K _ k.succ) (testcut (L n k) p b g.cared m s) a (district (L n k) g h w m s) i j):= by
  unfold armed; simp only [tagged_cost]; let u:=testcut (K n k) p a h.cared i j; let v : Works b u k.succ:= resident _ g h w i j
  rw [← S.rearr rotor,rotor_inv,on_labels]; congr 1; ext1 y; simp_rw [perm_app,testcut_v, tops,hop, scrap]
  rw [c,d n,flank]; simp only [smul_smul]; congr 1; ring -- check

lemma expand_inner (J T:placard X) (V Y:X) (x : Fin n→X) (k) (K L:Bills) {a b} {p : Test n} (g:Works b p k) (h : Works a p k) (q: Before b a)
    (r : Reaches S T L V Y):
    delta (K n k) p a h.cared (S.armed J (update x k Y)) = ∑ i : Axis,∑ j :Axis, delta (L _ k.succ) (testcut (K n k) p a h.cared i j) b (resident (K n k) g h q i j).cared (S.armed T (add (J i j) (update x k V))):= by
  unfold delta; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  have f:=r _ (add (J i j) x) k.succ _ _ (resident (K n k) g h q i j)
  rw [into,show update (add (J i j) x) k.succ V=add (J i j) (update x k V) by simp only [Fathom.add,← Fin.cons_update]] at f; exact f

lemma transpose' (f : Axis→Axis→Axis→Axis→ℂ) : (∑ i:Axis,∑ j:Axis,∑ m:Axis,∑ s:Axis, f i j m s)=∑ m:Axis,∑ s:Axis,∑ i:Axis,∑ j:Axis,f i j m s:= by
  have he (i): (∑ j:Axis,∑ m:Axis,∑ s:Axis,f i j m s)=∑ m:Axis,∑ s:Axis,∑ j:Axis,f i j m s:= by rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]
  simp_rw [he]; rw [sum_comm]; exact sum_congr rfl fun i _=>by rw [sum_comm]

lemma comparative (J T:placard X) (V Y:X) (x : Fin n→X) {k} (K L:Bills) {a b} {p : Test n} (g:Works b p k) (h : Works a p k) (q: Before b a)
    (r : Reaches S T L V Y) (c:Client K) (d:Client L): delta (K n k) p a h.cared (S.armed J (update x k Y))=
      ∑ i :Axis,∑ j :Axis, delta (K _ k.succ) (testcut (L n k) p b g.cared i j) a (district (L n k) g h q i j) (S.armed J (add (T i j) (update x k V))) := by
  rewrite [expand_inner S J T V Y x k K L g h q r]; simp_rw [delta,shellflip S J T K L _ _ _ _ (update x k V) k c d g h q]; exact transpose' _

/-- Comparison (92), outer K here constant. Does not require any symbol
 for the two heads viewed as nested (e.g. would land in grade six).
 Delta J_k T_ij actually represented. Keep inner L even with x dependence. -/
lemma taxation (i : Axis) (J T A:placard X) (V Y Z:X) (v : Fin n→X) (K:Bills) {p : Test n} {a b c} {k}
    (h : Works b p k) (g:Works a p k) (l:Works c p k) (q:Before b a) (e:Before c b) (u: Client K)
    (y:Reaches S T K V Y) (z:Reaches S J (postage i) V Z) (t : ∀ m j,Reaches S J (postage i) (T m j) (A m j)):
    delta (ticket i) p a g.cared (S.armed J (update v k Y))=
      delta (K n k) p b h.cared (S.armed T (update v k Z))+delta (K n k) p b h.cared (S.armed A (update v k V)):= by
  let r:=update v k V
  have L:= comparative S J T V Y v (postage i) K h g q y (posted i) u
  change delta (ticket i) _ _ _ _=(∑ m:Axis,∑ j:Axis,delta (ticket i) _ _ _ _) at L
  rw [L, S.expand_inner T J V Z v k K _ l h e z]
  unfold delta -- expand for sum_congr
  rw [← sum_add_distrib]; apply sum_congr rfl; intro m _; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
  let f:= testcut (K n k) p b h.cared m j
  let wc: Works c f k.succ:= resident _ l h e m j
  let ga:=district (K n k) h g q m j
  let M:= fades a c; let w : Works M f (0 : Fin (n+1)) := rent _ h g l q e m j
  let R:=S.armed J (add (T m j) r)
  change delta (ticket i) f a ga R=delta (ticket i) f c wc.cared R+S.tagged r (A m j) f
  rw [parted ga wc.cared w.cared R]; congr 1
  have Q:= t m j (n+1) (add (0:X) r) (0:Fin (n+1)) f M w
  rw [show update (add (0:X) r) (0:Fin (n+1)) (T m j)=add (T m j) r by simp [Fathom.add]] at Q; exact Q.symm
end Palace
end YM.GaugeFieldConstruction.Fathom
