import YM.CF.BProof.Cabinet.Halo
import YM.CF.BProof.Pods.Allowance

/- uniform phase label from acceptance throughout required blocks. Correction root
anchors only call reference z via `central`. Paid predicates on active still. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){N:Side}(Y:S.Setup L a (More N) d y)
variable (T:PathData G)(θ:ℝ)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "wB"=> House.Season mH Y.c'
local notation "g₀"=> Y.g
variable (x x':Pod Y) (b:House.Block Y.yard Y.c')
def truck(r:ℕ) := House.ray mH b r
lemma ray_home_hide (x:B)(p:Y.yard.Col)(r:ℕ): bT Y p∈truck Y x r↔ Grid.dist (House.two mH x) (elder g₀ p.2) ≤r ∧ p.1= House.one mH x :=by
 rw [truck,ray_spec,clock]; have h:House.one mH (bT Y p)=p.1:=rfl; have hp: House.two mH (bT Y p)=elder g₀ p.2:= (by rw [bT,hide,two_place]); rw [h,hp]; constructor; rintro ⟨⟨v,p⟩,q⟩; exact ⟨p,q⟩; rintro ⟨v,q⟩; rw [q]; exact ⟨⟨by unfold Circle.δ; exact (Cube.d_id _).trans_le (Nat.zero_le _),v⟩,rfl⟩ -- tune `simp`
def cartL : Y.yard.Col := (House.one mH b,Grid.grow g₀ (House.two mH b))
lemma cart_eq : bT Y (cartL Y b)= b:=by unfold bT cartL hide; simp only [elder_grow]; exact place_house ..
abbrev stampY(p:Y.yard.Col) : Fin 5:= Brick.Act.tag mH g₀ (hide mH g₀ p) (x _) ⟨p,rfl⟩
abbrev central:=stampY Y x (cartL Y b)
lemma cent_eq{V:Finset (House.Block Y.yard Y.c')}(h:b∈V)(p:Spiced Y V x x'): central Y x b=central Y x' b:=by unfold central stampY; rw [p _ (show hide mH g₀ (cartL Y b)∈V from (by change bT Y _∈_; rw [cart_eq]; exact h))] -- tune hide vs bT
lemma column_stamp (p:Y.yard.Col): stampY Y x p=(tool Y x).mood (nX Y p.1) (nB Y p.1,p.2):= (Brick.Act.label₀ mH g₀ x p).symm
lemma green_dir (p:b∉ nearL Y x) {r:ℕ}(H:r+1≤ hNear)(q:Y.yard.Col)(t:bT Y q∈truck Y b r) : Green Y (tool Y x) q:=by
 apply disjoint_left.mpr; intro i l k; exact p ((halo_spec ..).2 ⟨i,l,ray_in mH hNear H (ray_net Y _ _ t k)⟩)
variable (H:T.Bounds c w R v)(k:θ∈Set.Icc (1/2) 2) (t:Cabinet.Ready P Y T θ x)(p:b∉ nearL Y x) {r:ℕ}
include H k p t
lemma good_stamp(q:Y.yard.Col)(u:bT Y q∈ truck Y b r)(k':r+1≤hNear): stampY Y x q=central Y x b:=by
 let V:=House.two mH b; let U:=House.one mH b; let X:=tool Y x
 obtain ⟨v,w⟩:= (ray_home_hide ..).1 u; change q.1=U at w; rw [column_stamp,central,column_stamp]; change X.mood (nX Y q.1) (nB Y q.1,q.2)=X.mood (nX Y U) (nB Y U,Grid.grow g₀ V); rw [w]; refine Setup.frozen P Y T θ X H k (nB Y U) q.2 (Manual.wall mH U) r _ (fun q p'=>?_) t.2.2.1 v -- wall .. tune
 rw [frame]; exact green_dir Y x b p k' (U,q) ((ray_home_hide ..).2 ⟨p',rfl⟩)
lemma fixed_here : (x b).1=Brick.virgin mH g₀ b (central Y x b):=by
 have hx:b∉sick Y x:= fun v=> p (halo_in Y hNear (sick Y x) v)
 apply Prod.ext; swap; · funext i; have hp:¬Brick.Act.SevereTag mH g₀ b (x b):=fun h=> hx ((sick_c ..).2 (Or.inl h)); exact Bool.eq_false_iff.mpr (fun l=>hp ⟨i,l⟩) -- tune
 funext i; have ht:bT Y i.val=b:=i.property; change Brick.Act.tag mH g₀ b (x b) i=central Y x b; rw [Brick.Act.card_c, ← good_stamp P Y T θ x b H k t p i.val (r:=0) (ht.symm ▸ ray_home ..) (by unfold hNear; omega),column_stamp]; rfl -- let? ht.symm ▸ ... rewrites wrong
lemma stand_bill : Brick.Act.earnTag mH g₀ b (x b):= ⟨central Y x b,fixed_here P Y T θ x b H k t p⟩
lemma central_busy : b∈bitL Y x↔ central Y x b≠0:=by
 have hx:b∉sick Y x:= fun v=> p (halo_in Y hNear (sick Y x) v)
 rw [bitL,Brick.Act.shakes,or_iff_right (show b∉Brick.Act.sick mH g₀ y x from hx)]; constructor
 · rintro ⟨i,g⟩ h; apply g; unfold Brick.Act.tag; rw [fixed_here P Y T θ x b H k t p,h]; rfl
 intro h; refine ⟨⟨cartL Y b,cart_eq ..⟩,fun v=> h ?_⟩; unfold Brick.Act.tag at v; rw [fixed_here P Y T θ x b H k t p] at v; exact v
lemma defaultL(Q:Cores Y r)(l: Q∈ recital Y r x)(t':hNear≤r) (u:b∈ sober Y r Q (fault Y r x Q)) : central Y x b ≠0∧ Brick.Act.earnTag mH g₀ b (x b):=⟨(central_busy P Y T θ x b H k t p).1 (excited Y r Q l (Finset.mem_sdiff.mp u).1),stand_bill P Y T θ x b H k t p⟩
end YM.CF.BProof.Cabinet
