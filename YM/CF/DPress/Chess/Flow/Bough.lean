import YM.CF.DPress.Chess.Flow.Law
import YM.CF.Skye.Bent
import YM.CF.Scree.Locus
/-! Forest compression symmetry. The uniform law over Forest factors over
 parent blocks. Here prove with the splice involution rather than naming a sampler
 per block. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Transit.Bough
open Function Filter Lattice RG Precision Tree Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Cube
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
variable {n m:Side} (G:Ratio n m) (X:Support n)
def twig : Support m:= Finset.univ.filter fun i=> G.parent i∈ X
lemma twig_v {i}: i∈ twig G X ↔ G.parent i∈ X:=by simp [twig]
abbrev Wrap(F:Forest G)(i:Site m):= (F.up i,F.height i)
def Counts : Setoid (Forest G):= FD.Cash.ruleFx (fun x:Forest G=> fun i:↥(twig G X)=> Wrap G x i.val)
lemma size_p {X Y:Support n}(v:X⊆Y): twig G X⊆ twig G Y:= fun _ t=> (twig_v ..).2 (v ((twig_v ..).1 t))
lemma holds(F Y:Forest G): (Counts G X).r F Y ↔∀ i: Site m,G.parent i∈ X→Wrap G F i=Wrap G Y i:= ⟨fun p i v=>congrFun (show _ from p) ⟨i,(twig_v ..).2 v⟩,fun p=> funext fun i:↥(twig G X)=>p i.val ((twig_v ..).1 i.property)⟩ -- tune
lemma S_ext (F F':Forest G)(h:∀ i,Wrap G F i=Wrap G F' i): F=F':=by
 have ht:F.up=F'.up:=funext fun i=>congrArg Prod.fst (h i); have he:F.height=F'.height:=funext fun i=>congrArg Prod.snd (h i); cases F; cases F'; congr
def bond (T U:Forest G) : Forest G where
 up i:= if G.parent i ∈ X then T.up i else U.up i
 height i:= if G.parent i∈ X then T.height i else U.height i
 bound i:=by split; exact T.bound _; exact U.bound _
 rise i h:=by by_cases g:G.parent i∈X; · rw [if_pos g, T.stays i h,if_pos g,if_pos g]; exact T.rise i h
              rw [if_neg g,U.stays i h,if_neg g,if_neg g]; exact U.rise i h
 stays i h:=by split; exact T.stays i h; exact U.stays i h
lemma bond_v(i:Site m)(U V:Forest G):Wrap G (bond G X U V) i= if G.parent i∈ X then Wrap G U i else Wrap G V i:=by unfold Wrap bond; split <;>simp[*] -- tune
lemma bright(F Y:Forest G): (Counts G X).r (bond G X F Y) F := (holds ..).mpr fun i v=> by rw [bond_v,if_pos v]
lemma late {Y:Support n}(p:Disjoint X Y)(G' Gp:Forest G): (Counts G X).r (bond G Y G' Gp) Gp:=(holds ..).2 fun i t=> by rw [bond_v,if_neg (Finset.disjoint_left.mp p t)]
def windm : Equiv.Perm (Forest G × Forest G) :=by
 let f(Z:Forest G× Forest G):= (bond G X Z.2 Z.1,bond G X Z.1 Z.2); have h(Z:Forest G× Forest G):f (f Z)= Z:=by
    apply Prod.ext <;> apply S_ext <;> intro i; all_goals dsimp only [f]; all_goals simp_rw [bond_v]; all_goals split_ifs<;>rfl
 exact ⟨f,f,h,h⟩
variable [Nonempty (Forest G)] -- Measurable top instance
scoped instance :MeasurableSpace (Forest G):=⊤
scoped instance :MeasurableSingletonClass (Forest G):=⟨fun _=>trivial⟩
variable (A : Forest G)
abbrev cashT:= (FD.Cash.be_J (I:=Forest G))
abbrev St:= (cashT G).PM
lemma rwI {I:Type*}{x y z:I}(T:Setoid I)(p:T.r x y): T.r x z↔ T.r y z:=⟨fun i=>T.iseqv.trans (T.iseqv.symm p) i,fun i=> T.iseqv.trans p i⟩
lemma pair_t {Y:Support n}(h: Disjoint X Y) : (cashT G).Pair (Counts G X) (Counts G Y):=by
 intro i j; let T:=Counts G X; let S:=Counts G Y; let H:= cashT G; let Z:=FD.Cash.duo H H; let Q:=windm G Y; let P: (Forest G ×Forest G)→Prop:=fun x=> T.r x.1 i∧ S.r x.1 j; let L: (Forest G ×Forest G)→Prop:=fun x=>T.r x.1 i ∧ S.r x.2 j
 have ht(x): P (Q x)=L x:= propext (and_congr (show T.r (bond G Y x.2 x.1) i↔ T.r x.1 i from (rwI T (late G X h _ _))) (show S.r (bond G Y x.2 x.1) j↔ S.r x.2 j from rwI S (bright ..))) -- add helper
 have hg: Z.turn L= Z.turn P:=by
    unfold FD.Cash.turn; simp only [Finset.sum_filter]; conv_rhs=>rw [←Equiv.sum_comp Q]; -- closes?
    apply Finset.sum_congr rfl; intro i _; simp_rw [ht]; split_ifs <;> rfl
 have hv:= Z.tape (P:=P) (Q:=fun x=> (T.r x.1 i ∧ S.r x.1 j) ∧ (fun _:Forest G=>True) x.2) (fun i=>by simp [P]);  rw [(H.shade H (fun x=> T.r x i ∧ S.r x j) (fun _=>True)),FD.Cash.mint,mul_one] at hv; exact hv.symm.trans (hg.symm.trans (H.shade H (fun x=> T.r x i) (fun x=> S.r x j)))
end YM.CF.DPress.Chess.Transit.Bough
