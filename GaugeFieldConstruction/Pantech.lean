import GaugeFieldConstruction.GallKi
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I J α β:Type}[Fintype I][LinearOrder I][Fintype α][Fintype β]
section
variable {n:Side}
structure Isle (I:Type) (α β:Type)(n:Side) where
   X : α→Hub n
   F : α→ InkD n
   U : β→ Force n
   Y : β→ Copy n
   W : α→ List I
   B : β→ List I
variable (B:Isle I α β n)(p:Hub n)(S:List I)(s:Sect I)
structure Isle.Load (p:BudgetPoint)(σ:I→Seat n)(r h:ℝ)(k:ℕ)(V:α→ℝ)(Y:β→ℝ): Prop where
    med(i): Medal p (B.X i).val.2 ∅ (oV (B.F i)) h (Bplain (B.W i).length (V i) r)
    curve(i) : Medal p (B.U i).val.1.val.2 (B.U i).val.2 (B.Y i) h (Bplain (B.B i).length (Y i) r)
    form(i)(x): B.Y i x≠0 → sealI B.U i⊆ flags p.threshold x.1 ∧ Lattice.halo k (B.U i).val.2⊆plateI B.U i
    refs(i): B.F i ≠0→ Pub σ (B.W i).toFinset (B.X i).val.2
    rolls(i): B.Y i≠0→ Pub σ (B.B i).toFinset (plateI B.U i)
namespace Isle
abbrev UV(B:Isle I α β n)(i:α):Support (More n):=(B.X i).val.2
-- seeds
local notation "ρ"=> s.reg.length
local notation "Γ"=> Fin s.reg.length
abbrev boon (k:Fin s.reg.length) := s.reg.get k
def noteV (S:List I)(t : List I)(i:α)(D:Support (More n)):InkD n:= if knowR (B.W i) S t ∧ Disjoint (B.UV i) D then B.F i else 0
def oracle (i:Finset β):Copy n:= if knowR (rosterF i B.B) S s.pack then ∏ j∈i,B.Y j else 0
def purseV (i:α):= ditch (B.W i) S
def tressV (i:Finset β):= ditch (rosterF i B.B) S
variable (μ:ℝ) (u:Night S s)(K:I)
local notation "R"=> Heart p (B.UV) s.reg.length
local notation "H"=> Legist p (B.UV) s.reg.length
local notation "σV" i:max=> rosterF univ (fun q:Fin s.reg.length=>B.purseV S (i q))
local notation "ΩΠ" x:max d:max=> (∏ j:Fin s.reg.length, B.noteV S (boon s j) (x j) d)
include u
noncomputable def salt_Four: Grotto I B.UV B.U:=⟨p,_,u.holds,decide (s.pack ≠ []),fun x=> K :: (σV x.val),fun x=> μ • ΩΠ (x.val) ∅,fun x i=> K :: ((σV x.val)++ B.tressV S i),fun x i=> μ • ((oV (ΩΠ x.val (til B.U i))) * B.oracle S s i)⟩ -- oV may annotation
local notation "A"=> B.salt_Four p S s μ u K
variable (σ:I→ Seat n)(C:BudgetPoint)(h:ℝ)(k:ℕ)(V:α→ℝ)(U:β→ℝ)(v:Isle.Load B C σ 1 h k V U)(ht:0≤ V)(hp:0≤U)(t:0≤h)(g:0≤μ)(pK:σ K∈p.val.2)
include ht hp t g v pK
omit u g hp pK
lemma shop_f (T:List I)(i:α)(X D:Support (More n))(p:B.UV i⊆ X): Medal C X D (oV (B.noteV S T i D)) h (V i):=by
 unfold noteV; split
 next h=>
    have hw : B.UV i \ ∅ ⊆ X\ D:=fun x u=> let w:= (mem_sdiff.mp u).1; Finset.mem_sdiff.mpr ⟨p w,fun e=>Finset.disjoint_left.mp h.2 w e⟩
    have H':=Medal.stretchB (v.med i) p (empty_subset _) hw; rwa [Bplain,one_pow,div_one] at H'
 exact Medal.big (show Medal C X D (oV (0:InkD n)) _ 0 from Medal.zeroT) (ht i)
omit ht t
lemma shop_fV (T:List I)(i:α)(D:Support (More n))(p:B.noteV S T i D≠0): poke_F σ (B.UV i) (B.purseV S i).toFinset:=by
 have he: B.F i ≠0:=by unfold noteV at p; split at p; exact p; contradiction
 intro x t; exact (v.refs i he).2 x (List.mem_toFinset.mpr (List.mem_filter.mp (show x∈List.filter _ (B.W i) from List.mem_toFinset.mp t)).1)
omit v in
private lemma porM {T M:Type}[CommMonoidWithZero M](S:Finset T)(F:T→M)(i:T)(p:i∈S)(h:(∏ j∈S,F j)≠0):F i≠0:=fun e=> h (prod_eq_zero p e)
-- avoid section `include v` dropping. 
include u g ht hp t pK
set_option maxHeartbeats 400000 in
lemma salt_P : (A).Pits σ μ V U C 1 h k:=by
 have H'(x:R)(j:Γ):B.UV (x.val j)⊆ (H x).val.2:= fun i t=> mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,t⟩)
 have Η(x:R):p.val.2⊆(H x).val.2:= subset_union_left
 have Rv(x:Fin s.reg.length→α)(D:Support (More n)): oV (ΩΠ x D)=(∏ j:Γ,oV (B.noteV S (boon s j) (x j) D)):=by funext y; unfold oV; rw [Finset.prod_apply,Finset.prod_apply] -- tune
 have hw(x:R)(T D:Support (More n))(u:(H x).val.2⊆ T): Medal C T D (oV (ΩΠ (x.val) D)) h (∏ j:Γ,V (x.val j)):=by
    rw[Rv]; exact Medal.prodP _ _ _ (fun i _=> shop_f B S σ C h k V U v ht t (boon s i) _ _ D ((H' x i).trans u)) t
 have hu(x:R)(T D:Support (More n))(u:(H x).val.2⊆ T)(h: ΩΠ (x.val) D≠0)(i:I)(p:i∈ rosterF univ (fun q:Γ=> B.purseV S (x.val q))) : σ i∈ T:=by
    obtain ⟨j,_,l⟩:= (roster_mem ..).1 p; exact u (H' x j ((shop_fV B S σ C _ _ V U v (boon s j) _ D (porM _ _ j (mem_univ _) h)) i (List.mem_toFinset.mpr l)))
 refine ⟨⟨fun x t e=> ?_,fun x t e a=>?_⟩,⟨fun x y z=>?_, fun x y w a=>?_⟩,g⟩ -- t shadow binder syntax
 · unfold PitR Bplain; rw [one_pow,div_one]; have hx:= (hw x _ ∅ (subset_refl _)).rum μ; rw[Real.norm_of_nonneg g] at hx; exact hx
 · constructor
   · exact mem_filter.mpr ⟨mem_univ _,pays_z σ t⟩
   intro i b; obtain hi:= List.mem_toFinset.mp b
   rcases List.mem_cons.mp hi with l|l
   · rw[l]; exact Η x pK
   apply hu x _ ∅ (subset_refl _) _ i l; intro h; apply a; change μ • _= _; rw[h,smul_zero]
 · let Y:=y.val; let L:=mixedHub (H x) B.U Y; let z':= Y; let Θ:= til B.U Y; let X:=L.val.2; let St:= ∏ j∈Y,U j; let Hv:= oV (ΩΠ x.val Θ); let V':=B.oracle S s Y; have hX:(H x).val.2⊆ X:=subset_union_left
   change Medal C X Θ (μ • (Hv * V')) h _ ∧ _
   have C0(j)(p:j∈Y): sealI B.U j ⊆ Θ:=fun i e=> mem_biUnion.mpr ⟨j,p,e⟩
   have Z(j)(p:j∈Y):plateI B.U j ⊆ X:=fun i e=> mem_union_right _ (mem_biUnion.mpr ⟨j,p,e⟩)
   constructor
   · have V₀:Medal C X Θ V' h St:=by
        unfold V' oracle; split; swap; · exact Medal.big Medal.zeroT (prod_nonneg fun i _=> hp _)
        refine Medal.prodP _ _ _ (fun j h=> ?_) t
        have f:=v.curve j; rw[Bplain,one_pow,div_one] at f; refine f.stretchB (Z j h) (C0 j h) ?_; -- shadow h
        intro w e; obtain ⟨a,b⟩:=mem_sdiff.mp e; apply Finset.mem_sdiff.mpr; refine ⟨Z j h a,fun k=> b ?_⟩; change _∈ sealI B.U j; rw[← ((show BasisI B.U (H x) (decide (s.pack≠[])) Y from y.property).distinct.foot B.U h)] -- tune
        exact mem_inter.mpr ⟨a,k⟩
     rw [Bplain,one_pow,div_one]; have f:= ((hw x X Θ hX).cross V₀ t).rum μ
     rw[Real.norm_of_nonneg g,← mul_assoc] at f; exact f
   intro b k'; have hx:V' b≠0:= fun e=> k' (show μ • (Hv b*V' b)=0 from (by rw [e,mul_zero,smul_zero]))
   unfold V' oracle at hx; split at hx; swap; · exact False.elim (hx rfl)
   have f(j)(p:j∈Y):=v.form j b (porM _ _ j p (show ∏ j∈Y,B.Y j b≠0 from (fun e=> hx (by rw[Finset.prod_apply,e]))))
   constructor
   · intro i e; obtain ⟨j,g,h⟩:=mem_biUnion.mp (show i∈ Θ from e); exact (f j g).1 h
   intro i a; change i ∈ Lattice.halo k Θ at a; -- halo simp
   unfold Lattice.halo at a; obtain ⟨d,h,z⟩:=mem_filter.mp a|>.2|>.elim fun i u=> Exists.intro i (mem_filter.mp u); obtain ⟨j,u,p⟩:= mem_biUnion.mp h; refine Z j u ((f j u).2 (mem_filter.mpr ⟨mem_univ _, ⟨d,mem_filter.mpr ⟨p,z⟩⟩⟩)) 
 · constructor
   · exact mem_filter.mpr ⟨mem_univ _,pays_z σ w⟩
   intro i b; let T:=til B.U y.val; let X:=mixedHub (H x) B.U y.val; let J:=ΩΠ (x.val) T; let B':=B.oracle S s y.val
   have V':J≠0:=fun t=> a (show μ • (oV J*B')=0 from (by rw[t]; exact smul_eq_zero_of_right _ (zero_mul _)))
   have ht':B'≠0:=fun t=> a (show μ • (oV J*B')=0 from (by rw[t,mul_zero,smul_zero]))
   rcases List.mem_cons.mp (List.mem_toFinset.mp b) with c |(c: _ ∈ (σV (x.val))++B.tressV S y.val)
   · rw[c]; exact mem_union_left _ (Η x pK)
   rcases List.mem_append.mp c with c|c
   · exact mem_union_left _ (hu x _ _ (subset_refl _) V' i c)
   unfold B' oracle at ht'; split at ht'; swap; · contradiction
   obtain ⟨j,v₀,g⟩:= (roster_mem ..).1 (List.mem_filter.mp c).1
   have hp:=porM (y.val:Finset β) _ j v₀ ht'; exact mem_union_right _ (mem_biUnion.mpr ⟨j,v₀,(v.rolls j hp).2 i (List.mem_toFinset.mpr g)⟩)
end Isle
end
end Iona
end YM.CF.Scree.Ing
end
