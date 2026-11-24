import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable(G:Ratio N P)
section
variable {α:Type}[Fintype α][LinearOrder α]
lemma jet_sum (w: Finset ι)(V:ι→Op α)(s:Bool): Thera.jazz s (∑ i∈w,V i)= ∑ i∈w, Thera.jazz s (V i):=by cases s; rfl; simp [Thera.jazz, Finset.sum_neg_distrib]
lemma jazz_v (w:Op α)(s b:Bool):Thera.jazz s (Thera.jazz b w)= Thera.jazz (s.xor b) w:=by cases b<;>cases s<;>simp [Thera.jazz]
end
lemma packV(b:Bool)(w:Op (Iota G)): summit (patchQ G) (Thera.jazz b w)= Thera.jazz b (summit (patchQ G) w):=by cases b <;> rfl
lemma rune (z:ℂ)(F:Op (Iota G)): summit (patchQ G) (z • F)= z •summit (patchQ G) F:=rfl
lemma summa (w: Finset ι)(V:ι→Op (Iota G)): summit (patchQ G) (∑ i∈w,V i)=∑ i∈w,summit (patchQ G) (V i):=by ext; unfold Fock.summit; simp [Matrix.sum_apply]
lemma whisky(x:Op (Single N)): summit (patchQ G) (endorse G x)= x:=by
 ext i j; unfold summit endorse; change extendK _ _ _ _= _; rw [extendK,if_pos (?_:en G (patchQ G i) ∧ en G (patchQ G j))]; rfl; exact ⟨en_ride ..,en_ride ..⟩ -- tune
local notation "σ"=> Single N
local notation "s₀"=> summit (patchQ G)
def helm (b:Sweep N)(v:Op (Iota G)):= Thera.jazz (accent b) (toSpin G b v)
lemma hoodX(j:Sweep N)(p:Op (Iota G)): s₀ (helm G j p) = yank j.charge (castX j) (spinU j.charge j.s) (s₀ p):=by unfold helm yank; rw [packV,show s₀ (toSpin G j p)=_ from everyK G ..]; rfl -- tune
lemma juice(j:Sweep N)(p:Op (Iota G))(b:Bool):toSpin G j (Thera.jazz b p)= Thera.jazz b (toSpin G j p):=by
 cases b; rfl; change sings _ _ (-star _)= -star _; rw [singT,win_n,win_s,map_neg,map_star]; rfl
lemma year (h:Odd G.count.val)(j k:Sweep N)(v:Op (Iota G)): helm G k (helm G j v)= helm G (j*k) v:=by unfold helm; rw [juice,jazz_v, Bool.xor_comm, skim G h,show accent (j*k)=(accent j).xor (accent k) from det_p ..]
lemma helm_i (h:Odd G.count.val) (v:Op (Iota G)): helm G 1 v=v:=by unfold helm; rw [skey G h,show accent (N:=N) 1=false from det_i]; rfl
abbrev glade (U:NoteS G e): Meter Bool G e:=fun b S x=>if b then Thera.jazz b (U S (chillF G e x)) else U S x
def salsa(U:NoteS G e)(S:Seal (Site (More P)))(v:cro G e): Op (Single N):= s₀ (ced G e Bool.xor (glade _ U) false S v)
lemma asp (h:Odd G.count.val)(U:NoteS G e)(S:Seal (Site (More P)))(v:cro G e)(b:Bool)(p:chillF G e v=v): ced G e Bool.xor (glade _ U) b S v=Thera.jazz b (ced G e Bool.xor (glade _ U) false S v):=by
 unfold ced; have he(k:Sweep N):modeT G e k Bool.xor (glade _ U) b S v=Thera.jazz b (modeT G e k Bool.xor (glade _ U) false S v):=by
    unfold modeT coda Levier.perch; rw [←juice]; unfold glade; simp_rw [wish_f,p]; cases b<;> cases l:accent k<;>simp [l,jazz_v, Thera.jazz] -- unfold toWish
 have hh:= (Finset.sum_congr (s₁:=Finset.univ) rfl fun k _=> he k).trans (jet_sum _ _ _).symm
 rw [hh]
 cases b; rfl; simp [Thera.jazz,pic]
lemma vista(h: Odd G.count.val)(U:NoteS G e)(S: Seal (Site (More P)))(v:cro G e)(g:chillF G e v=v)(k:Sweep N):salsa G U (toRoar G k⁻¹ S) (toWish G e k v)= yank k.charge (castX k) (spinU k.charge k.s) (salsa G U S v):=by
 let H:= ced G e Bool.xor (glade G U); let X:= toWish G e k v; have he: toSpin G k (H false S v)= Thera.jazz (accent k) (H false (toRoar G k⁻¹ S) X):=by rw [show toSpin _ _ _=_ from shineB G h e k Bool.xor (glade _ U) Bool.xor_assoc Bool.xor_false S v false]; simp_rw [Bool.false_xor]; exact asp G h U _ X _ (by unfold X; rw [wish_f,g]) -- tune
 unfold salsa; rw [← hoodX G k]; unfold helm; change s₀ (H false _ X)= s₀ (Thera.jazz _ (toSpin G k (H false _ v))); rw [he,jazz_v,Bool.xor_self]; rfl
lemma gemX(h:Odd G.count.val)(U:NoteS G e)(V:Raw (cro G e) (Iota G))(W:Op (Single N))(p:∀ x,∑ i,U i x= V x)(x:cro G e)(hx:chillF G e x=x)(H:∀ k:Sweep N, s₀ (V (toWish G e k x))= yank k.charge (castX k) (spinU k.charge k.s) (s₀ (V x))): (∑ i,salsa G U i x)= s₀ (V x):=by
 let M:= s₀ (V x)
 have he(k:Sweep N): (∑ i, s₀ (modeT G e k Bool.xor (glade _ U) false i x))=M:=by
    unfold modeT coda Levier.perch; let w:=toWish G e k x; rw [←summa,← toSpin_sum _ h]; have hw:chillF G e w=w:=by rw [show chillF G e w= _ from wish_f ..,hx]
    have hx(y:Seal (Site (More P))): glade G U (false.xor (accent k)) y w=Thera.jazz (accent k) (U y w):=by unfold glade; rw [hw]; cases v:accent k<;> rfl
    change s₀ (toSpin G k⁻¹ (∑ i,glade G U _ _ w))= _; simp_rw [hx,←jet_sum]; rw [show (∑ i:Seal (Site (More P)),U (toRoar G k⁻¹ i) w)=V w from (Equiv.sum_comp (weaveS G k⁻¹) (fun i=>U i w)).trans (p w)]
    rw [juice,← kox G h]; change s₀ (helm G k⁻¹ (V w))=_; rw [hoodX,show s₀ (V w)=_ from H k,← hoodX _ k,← hoodX _ k⁻¹, year G h k k⁻¹, mul_inv_cancel,helm_i G h]
 unfold salsa ced; simp_rw [rune,summa,← Finset.smul_sum]; rw [sum_comm]; simp_rw [he, sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ]; unfold pic; push_cast; rw [smul_smul,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=Sweep N)),one_smul]
end YM.CF.Hest
