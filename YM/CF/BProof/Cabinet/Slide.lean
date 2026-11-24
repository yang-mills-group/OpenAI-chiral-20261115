import YM.CF.BProof.Cabinet.Vote

/- Gold & FAR acceptance by treads. r≤spec plan. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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
local notation "g₀"=> Y.g
local notation "wB"=> House.Season mH Y.c'
variable (x x':Pod Y)(b:B)
abbrev bT(q:Y.yard.Col) := hide mH g₀ q
abbrev roadB(p: Site (More N)) := addr mH g₀ p
abbrev parcelT:= soil P Y
abbrev Cores(r:ℕ):= Tower.CoreX wB r
abbrev recital(r:ℕ):= Contour.Season.chooseE r (bitL Y)
variable (H:T.Bounds c w R v)(k:θ∈Set.Icc (1/2) 2)(q q':Y.yard.Col)
lemma walks (p:(Gauss.base mH).N q q' 1): Grid.dist (bT Y q) (bT Y q')≤1:= near_hide mH g₀ q q' 1 ((Gauss.base mH).mono (by rw [one_mul]; exact Y.g.count.property) p)
lemma chrono : (parcelT P Y).horizon'=steady c Y.yard.short S.M R y:= (pulse P Y).p_hor S.K S.P c S.M R Y.yard y S.κ -- order?
-- Lamp reading
lemma bloom_X {V:Finset (House.Block Y.yard Y.c')}(p:beams V x x')(u: ray mH (bT Y q) 2 ⊆ V): Bloom P Y T θ x q= Bloom P Y T θ x' q:=by
 let A:= parcelT P Y; let i:=nX Y q.1; let t:=nB Y q.1
 let Sx:=tool Y x; let Sy:=tool Y x'
 have he : Pawn.Agreed g₀ Sx Sy V:= Brick.Act.agrees mH g₀ p
 have hQ:Setup.owner Y (i:=i) t q.2=q:=frame Y q.1 q.2
 have hx(k:ℕ)(v:k≤2+A.horizon'):Pawn.Shade g₀ V q k:=by
    apply House.ray_loan mH g₀ V 2 _ u; refine v.trans ?_; rw [show A.horizon'=steady c Y.yard.short S.M R y from chrono P Y]; have hz:= cover P Y; omega
 apply congrArg₂ And
 · unfold Snuff; rw [he.sev _ (u (ray_home ..)),Pawn.local_level g₀ _ _ V y T θ (soil P Y) (room P Y) q he (hx _ (by change A.horizon'≤_; omega))]
 apply congrArg₂ And
 · apply Pawn.ticket_mood g₀ Y.hall Sx Sy V y T θ A (room P Y) he (Manual.wall mH q.1) t q.2; rw [show (location mH i t,q.2)=q from hQ]; exact hx _ (by omega)
 apply congrArg (fun f:TAxis→Prop=>∀i,f i); apply funext; intro j; apply Pawn.ticket_move g₀ Y.hall Sx Sy V y T θ A (room P Y) he (Manual.wall mH q.1) t q.2 _ j; rw [show (location mH i t,q.2)=q from hQ]; exact hx _ le_rfl
-- auto
include H k
lemma blooms (p:bT Y q∉ Grid.collar (bitL Y x) 3): Bloom P Y T θ x q:=by
 let A:=bT Y q; let X:=tool Y x; let j:=nX Y q.1; let i:=nB Y q.1; let U:=soil P Y; have hu: ¬ Y.yard.D j:= Manual.wall mH q.1; let Z(z:Space (More N)):= Setup.owner Y (i:=j) i z
 have hv : Z q.2=q:= frame Y q.1 q.2; have hx(z:B)(u: Grid.dist A z≤2): z∉ bitL Y x:= fun e=> p (Grid.collar_mem.mpr ⟨z,e,Nat.le_trans u (by norm_num)⟩)
 have hy(z:B)(u: Grid.dist A z≤1) : Clear Y X 1 z := by
    apply disjoint_left.mpr; intro i v k; exact hx i ((Grid.triangle A z i).trans (Nat.add_le_add u ((ray_spec ..).1 k).1)) (enlargement Y x v) -- tune metavars
 have ha:Green Y X q:= hy A (by simp); have hq: Green Y X (Z q.2):= hv.symm ▸ ha
 have he(n:ℕ)(hh:n≤ Y.g.count.val): ∀ j,(Gauss.base mH).N q j n→ j∉Model.raw y mH X.sev X.gauss:= fun j u=> green Y X q ha j ((Gauss.base mH).mono hh u)
 have hf:= Pricing.Model.free S.K S.P c S.M R S.κ y mH T (pulse P Y) (room P Y) H k X.sev X.gauss X.gap q _ le_rfl (he _ (by have hh:=cover P Y; omega)) (ease P Y)
 have hp:q∉X.sev:=fun v=> he 0 (Nat.zero_le _) q ((Gauss.base mH).start ..) (mem_union_left _ v)
 have hs(z:Space (More N))(p:Grid.dist A (bT Y (Z z)) ≤ 2) : X.mood j (i,z)=0:= Eq.trans (Brick.Act.label mH g₀ x j i z hu) (Brick.Act.zero_tag mH g₀ y x _ (hx _ p) _)
 refine ⟨⟨fun p=>False.elim (hp p),fun p=>False.elim (hf (mem_filter.mpr ⟨mem_univ _,p⟩))⟩, (colorful P Y T θ X H k i q.2 hu hq).1,?_⟩
 intro l; let w:=q.2+tstep l; have ht:Grid.dist A (bT Y (Z w)) ≤1:=by
    change Grid.dist (bT Y q) _ ≤1; rw [← hv] -- tune q in q.2? w containing q
    apply walks; exact ⟨rfl,(show Grid.dist q.2 (q.2+tstep l)≤1 from Face.slide_t .. ▸ Grid.near_slide ..)⟩
 exact (fol P Y T θ X H k i q.2 hu l hq (hy _ ht)).2 ((hs q.2 (by rw [hv]; simp [A])).trans (hs w (ht.trans (by norm_num))).symm) -- tune argument order Fol
variable {r:ℕ}
def groupT(r:ℕ)(Q:Cores Y r)(x: Pod Y):=∀ q:Y.yard.Col, bT Y q∈ Grid.collar Q.val 3 → Bloom P Y T θ x q
def ore (v:5≤r): Gold r (bitL Y) (Ready P Y T θ) (lid Y):=by
 refine ⟨groupT P Y T θ r,?_,?_,?_⟩
 · intro Q; unfold groupT Virtue; simp_rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro q; apply MeasurableSet.iInter; intro p; exact bloom_m P Y T θ q -- tune binder Prop proof has countable
 · intro i x y p; refine propext (forall_congr' fun j=> ?_); have he(j:Y.yard.Col)(g:bT Y j∈Grid.collar i.val 3): ray mH (bT Y j) 2⊆Grid.collar i.val r:=by intro k u; obtain ⟨a,vH⟩:=ray_spec ..|>.1 u; apply Grid.collar_le Subset.rfl (show 2+3≤ r from v) (Grid.nearby ((Grid.dist_symm ..).trans_le a) g)
   -- goal in Hey binder no g. use case
   by_cases k:bT Y j ∈ Grid.collar i.val 3; · simp only [k,true_implies]; exact Iff.of_eq (bloom_X P Y T θ x y j (V:=Grid.collar i.val r) p (he j k))
   simp [k] -- tune
 intro x h; rw [authority]; refine ⟨fun H i _ j p=>H.2 j,fun g=>⟨h, fun q=>?_⟩⟩
 by_cases k':bT Y q∈ Grid.collar (bitL Y x) 3; swap; · exact blooms P Y T θ x H k q k'
 obtain ⟨b,v,h⟩:= Grid.collar_mem.mp k'
 rw [←Tower.coverE wB r (bitL Y x)] at v; obtain ⟨i,y,t⟩:= mem_biUnion.mp v; exact g i y q (Grid.collar_mem.mpr ⟨b,t,h⟩)
end YM.CF.BProof.Cabinet
