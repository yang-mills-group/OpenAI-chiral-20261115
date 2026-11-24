import GaugeFieldConstruction.Oracles

/-!
# U2 exact S-space product. Commuting left multipliers. U4 normalized brackets consequent formulas.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6500
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Row LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Module Record
open Floor
open scoped Topology BigOperators ContDiff
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n : ℕ}
local notation "l4"=>Calibration.lift Floor.four
local notation "l5"=>Calibration.lift Floor.five
namespace Supplies
variable {S : City} {P : Axis→Across} {p : Sheds S P} (q : Supplies p)
local notation "L" => Tot S P p
lemma rise (g : L) (u) (v : Fin n→UV five) (k) (J : Bulb) (f : Test n) (r:Works J f k) (a i): paid k i (S.spot v k (q.theta g a u)) f=
    delta (ticket a) f J r.cared (fun m j=> S.tagged (update v k (P i u)) (prints g.val m j)):= by
  rw [pays,q.law g u a n _ _ _ J (r.via _ (dband ..))]
  have he (m j:Axis): S.tagged (update v k (P i u)) (prints g.val m j)=paid k.succ i (armed S (prints g.val) (update v k (l4 u)) m j) := by
    unfold armed; rw [← into,← into _ v k _ (l4 u), ← p.money _ _ (n+1)]
  simp_rw [he]; rw [Delta_x]; rfl

lemma issued (t g : L) : ((0,Bend.cents _ (q.bend t) g.val):OneW × BothV) ∈ LinearMap.ker (readTest S) := by
  rw [LinearMap.mem_ker]; ext1 ⟨o,w⟩; ext1 ⟨a,j⟩; rw [read_v,audit,LinearMap.sub_apply,LinearMap.sum_apply]
  change ∑ i:Axis, paid front i (S.spot (other w) front (q.theta t a (pens g.val i j))) o.p- paid front a (S.spot (other w) front 0) o.p=0 -- parentheses adjust
  rw [map_zero,map_zero,LinearMap.zero_apply,sub_zero]
  have he i:= q.rise t (pens g.val i j) (other w) front o.a o.p o.u a i
  simp_rw [he,deconstant]
  rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro m _
  simp_rw [← S.into]; rw [← LinearMap.sum_apply,← map_sum]
  have ht:= Bend.payW p.toBend g.val j; rw [show Bend.sum P p.toBend g.val=0 from g.property] at ht
  rw [show (∑ i : Axis,P i (pens g.val i j))=0 from ht.symm,map_zero]; rfl

variable (H: Scope p)
include H
lemma manufacture (t g : L):∃ u :L, Bend.cents P p.toBend u.val=Bend.cents _ (q.bend t) g.val:= by
  have h : _∈LinearMap.range (around _ p.toBend):= (kernel_full p H) ▸ q.issued t g
  obtain ⟨u,h⟩:= h
  exact ⟨⟨u,(congr_arg Prod.fst h : _ = (0:OneW))⟩, congr_arg Prod.snd h⟩
lemma exactly : Injective (fun u:L => Bend.cents P p.toBend u.val):=fun T W e=>Subtype.ext ((precedes p H) (Prod.ext ((show Bend.sum _ p.toBend T.val=0 from T.property).trans (show Bend.sum _ p.toBend W.val=0 from W.property).symm) e))

def rax (t:L):L→ₗ[ℂ] L where
  toFun g:=(q.manufacture H t g).choose
  map_add' x y:= by
    apply exactly H; change Bend.cents P p.toBend _= Bend.cents P p.toBend ((q.manufacture H t x).choose.val+(q.manufacture H t y).choose.val); rw [map_add]; simp_rw [Exists.choose_spec (manufacture q H _ _)]; exact map_add _ x.val y.val
  map_smul' r x:= by
    apply exactly H; change Bend.cents P p.toBend _=Bend.cents P p.toBend (r • (q.manufacture H t x).choose.val); rw [map_smul, Exists.choose_spec (manufacture q H t x)]; exact (Exists.choose_spec (manufacture q H t (r • x))).trans (map_smul _ r x.val)
lemma earns (t g : L):Bend.cents P p.toBend (rax q H t g).val=Bend.cents _ (q.bend t) g.val:= Exists.choose_spec (q.manufacture H t g)
lemma patter (t g : L) (i j) : P i ((q.rax H t g).val.val j)= q.theta t i (g.val.val j):=congr_fun (congr_arg Subtype.val (earns q H t g)) (i,j)

def heart : L→ₗ[ℂ] L→ₗ[ℂ] L where
  toFun x:=q.rax H x
  map_add' x y:= by
    apply LinearMap.ext; intro z; apply exactly H; apply Subtype.ext; ext1 ⟨i,j⟩; change P i ((q.rax H (x+y) z).val.val j) =P i ((q.rax H x z).val.val j + (q.rax H y z).val.val j); rw [map_add,patter,patter]; rw [patter q H y z i j]; simp
  map_smul' r x:= by
    apply LinearMap.ext; intro z; apply exactly H; apply Subtype.ext; ext1 ⟨i,j⟩; change P i ((q.rax H (r • x) z).val.val j) = P i (r • (q.rax H x z).val.val j); rw [map_smul,patter,patter q H x z i j,map_smul]; rfl
lemma wanted (t g : L) (i j) : P i ((q.heart H t g).val.val j)=q.theta t i (g.val.val j):= patter q H t g i j
lemma conjugated (t g : L) : sbar p (q.heart H t g)=q.heart H (sbar p t) (sbar p g) := by
  apply exactly H; apply Subtype.ext; ext1 ⟨i,j⟩; change P i ((sbar p (q.heart H t g)).val.val j)=P i ((q.heart H (sbar p t) (sbar p g)).val.val j); rw [wanted, show P i ((sbar p (q.heart H t g)).val.val j)=shade five _ from (p.realD i ((q.heart H t g).val.val j)).symm,wanted _ _ t g, q.reality]; rfl

-- apply multiplication to contour with grade-five external charges
lemma twice (J : Bulb) (f : Test n) (x : Fin n→UV five) (k) (v:Works J f k) (t g z:L) (j i):
    delta (ticket i) f J v.cared (S.armed (prints t.val) (update x k (q.theta g i (z.val.val j))))=
      paid k i (S.spot x k (P i ((q.heart H t (q.heart H g z)).val.val j))) f:= by
  rw [wanted, rise _ _ _ _ _ J f v]; simp_rw [← q.wanted H _ _ i]; rfl -- loop check

lemma compatible (t g : L) : Commute (q.heart H t) (q.heart H g) := by
  let i : Axis:=0
  apply LinearMap.ext; intro z; apply Subtype.ext; apply sub_eq_zero.mp
  apply H.second i; intro j u f
  let o:=other u; let Y:L:=q.heart H t (q.heart H g z); let W:L:=q.heart H g (q.heart H t z)
  let V:=z.val.val j; let Tg:=q.theta g i V; let Tt:=q.theta t i V; let A:=fun m l=>q.theta t i (pens g.val m l)
  change paid front i (S.spot o front (P i (Y.val.val j-W.val.val j))) f.p=0; rw [map_sub,map_sub,map_sub,LinearMap.sub_apply]; unfold Y W; rw [← twice q H f.a _ _ front f.u,← twice q H f.b _ _ front f.v]
  apply sub_eq_zero.mpr
  have T := S.taxation i (prints t.val) (prints g.val) A (l4 V) Tg Tt o (postage i) f.v f.u f.w f.q f.r (posted i)
    (q.law g V i) (q.law t V i) (fun m l=>q.law _ _ i)
  have E (m l): S.armed A (update o front (l4 V)) m l= paid 0 i (S.armed (prints (q.heart H t g).val) (update o front (l4 V)) m l):= by
    have ht (x : Fin 2→UV five) (j :UV four): S.tagged x (P i j)=paid 0 i (S.tagged x (l4 j)):= p.money _ _ _ (Fathom.add 0 x) 0
    refine Eq.trans ?_ (ht _ (pens (q.heart H t g).val m l)); rw [show P i _=A m l from wanted q H t g i (ordered m l)]; rfl
  rw [funext fun (m : Axis)=> funext (@E m),show postage i _ front=ticket i from rfl, Delta_z f.v _ _ _ (stand p _ _),add_zero] at T; exact T

-- unit implies forms (101). bracket set for lift
omit H in
lemma is_five (x : UV five): l5 x=x := rfl
lemma spin_d (t : Tot S P p) (Ω i b) : q.Y five t Ω (P i b)-P i (q.Y four t Ω b)= ∑ j:Axis, (Ω.val j i:ℂ) • q.theta t j b:= by
  apply sub_eq_zero.mp; apply H.short; intro x f
  let v:=other x
  rw [map_sub,map_sub,map_sum,LinearMap.sub_apply,LinearMap.sub_apply,LinearMap.sum_apply]; simp_rw [map_smul,LinearMap.smul_apply] -- pay scalars
  rw [p.money,pays]; let Mv:=armed S (prints t.val) (update v front (l4 b)); change _- _= (0:ℂ)
  have E := q.decree five Ω t (P i b) _ v front _ _ f.u
  simp only [is_five] at E
  have Q:= q.decree four Ω t b _ v front _ _ (f.u.via _ (dband (direction front i) f.p))
  change S.spot v front (q.Y four t Ω b |> l4) _=_ at Q -- check
  have M j:= q.law t b j _ v front _ _ f.u
  have ht : S.armed (prints t.val) (update v front (P i b))=fun m l=> paid front.succ i (Mv m l):= by
    funext m l
    have he:=p.money i b (2+1) (Fathom.add (prints t.val m l) v) front.succ
    rw [into,into] at he; exact he
  change S.spot v front _ f.p- - S.spot v front (l4 _) _ - (∑ j:Axis,_ • S.spot v front _ f.p)=0 -- binder m?
  rw [E,Q,ht]; simp_rw [M]; rw [show rpm Ω 2 front=desk front Ω from rfl, Delta_x']; simp only [Complex.real_smul]; change _ - - delta _ _ _ _ Mv - ∑ j:Axis, (Ω.val j i:ℂ) • delta (ticket j) f.p f.a f.u.cared Mv=0; simp only [smul_eq_mul]; abel

lemma once (t : Tot S P p) (i b) (z : L) (h:q.heart H t=1) : q.theta t i (z.val.val b)=P i (z.val.val b) := by rw [← q.wanted H t z,h,Module.End.one_apply] -- implicit L shadow
lemma twirling (t : Tot S P p) (h:q.heart H t=1) (Ω i b) : q.Y five t Ω (q.theta t i b)- q.theta t i (q.Y four t Ω b)= ∑ j:Axis,(Ω.val j i:ℂ) • q.theta t j b:= by
  apply sub_eq_zero.mp; apply H.short; intro v f
  let x:=other v
  let J:=prints t.val; let T:=armed S J (update x front (l4 b)); let A:= fun m l=> P i (pens t.val m l); let Z:=q.theta t i b; let Y:=q.Y four t Ω b
  have X m l:Reaches S J (postage i) (J m l) (A m l):= by
    have he:=q.law t (t.val.val (ordered m l)) i; rw [q.once _ _ _ _ _ h] at he; exact he
  have U:=S.taxation i J J A (l4 b) (l4 Y) Z x (rpm Ω) f.v f.u f.w f.q f.r (tilted Ω) (q.decree four Ω t b) (q.law t b i) X
  have E : S.armed A (update x front (l4 b))=fun m l=>paid 0 i (T m l):= funext fun m=> funext fun l=> p.money _ (t.val.val (ordered m l)) _ (Fathom.add 0 _) 0 -- check
  have V:= q.law t Y i _ x front _ _ f.u
  have W:= q.decree five Ω t Z _ x front _ _ f.v
  simp only [is_five] at W
  have M j:= q.law t b j _ x front _ _ f.v
  rw [show postage i 2 front=ticket i from rfl] at V; rw [← V, ← W, E, show rpm Ω 2 front=desk front Ω from rfl, Delta_z' f.v T i Ω (stand p _ _)] at U
  rw [map_sub,map_sub,map_sum,LinearMap.sub_apply,LinearMap.sub_apply,LinearMap.sum_apply]; simp_rw [map_smul, LinearMap.smul_apply, show other v=x from rfl, M]
  change S.spot x front _ _-S.spot x front (q.theta t i Y) f.p- _=0; rw [U]
  simp only [Complex.real_smul]; change S.spot x front (q.Y five t Ω Z) f.p-(S.spot x front (q.Y five t Ω Z) f.p+ -(∑ j:Axis,(Ω.val j i:ℂ) • delta (ticket j) f.p f.b f.v.cared T)) - (∑ j:Axis,(Ω.val j i:ℂ) • delta (ticket j) f.p f.b f.v.cared T)=0
  abel
end Supplies
end YM.GaugeFieldConstruction.Ember
