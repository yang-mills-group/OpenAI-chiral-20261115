import GaugeFieldConstruction.Dawn3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000
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
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
set_option linter.flexible false
variable {n:Side}{ι γ τ E:Type}[Fintype ι][LinearOrder ι][NormedAddCommGroup E][NormedSpace ℝ E]
open Drapes Tenant Palot
attribute [local instance] loreM loreN
namespace Ladder3
section lint
variable {p r:Bool} {n:Side} {S V:Support (More n)}{H:BudgetPoint}{h c b:ℝ} {D:Support (More n)}
local notation "LN"=> Orbit n→FC (Dwell n)
variable {F G: Orbit n→ FC (Dwell n)}
lemma camp_b (f:S⊆ V):camp S ⊆ camp V:=fun _ q=> mem_filter.mpr ⟨mem_univ _,f (mem_filter.mp q).2⟩
lemma opTheme0 (S:Support (More n))(p:Bool) : OpTheme S 0 p:=⟨fun _ _ _ _=>rfl,fun _=> Fock.Sector.zero _,measurable_const,fun _ g=> (show sauce false false (tradew n g) (0:FC (Dwell n))=0 from map_zero _).symm⟩ -- inspect Sector.zero
lemma opThemePass (g:OpTheme S F p)(f:S⊆ V): OpTheme V F p:=⟨fun i j a b=>g.same i j (fun _ v t=>a _ (f v) (f t)) (fun _ v=> b (f v)),fun i=> lift_v (g.lit i) (camp_b f),g.keep,g.gait⟩
lemma opThemeScale (u:ℂ)(g:OpTheme S F p): OpTheme S (u • F) p:=⟨fun i j a b=> congrArg (u • ·) (g.same i j a b),fun i=> (g.lit i).scale _,g.keep.const_smul u,fun i t=> by
 change u • _ = twist _ (u • F i); rw [twist_scalar,g.gait]; rfl ⟩ -- tune
lemma opThemePlus(t:OpTheme S F p)(v:OpTheme S G p):OpTheme S (F+G) p:=⟨fun i j a b=>congrArg₂ (·+·) (t.same i j a b) (v.same i j a b),fun i=> (t.lit i).add (v.lit i),t.keep.add v.keep,fun i b=>(congrArg₂ (·+·) (t.gait i b) (v.gait i b)).trans (show sauce false false _ (F i+G i)=_ from map_add _ _ _).symm⟩ -- tune opacity
lemma opThemeTimes(t:OpTheme S F p)(v:OpTheme S G r):OpTheme S (F*G) (p.xor r):=⟨fun i j a b=>congrArg₂ (·*·) (t.same i j a b) (v.same i j a b),fun i=>(t.lit i).mul (v.lit i), t.keep.mul v.keep,fun i g=>(congrArg₂ (·*·) (t.gait i g) (v.gait i g)).trans (show sauce false false _ (F i*G i)=_ from singm ..).symm⟩
lemma opThemeHold (F:Copy n)(p:ThemeR S F): OpTheme S (fun i=> (F i).val) false:=⟨fun i j a b=>congrArg Subtype.val (p.same i j a b),fun i=>life (p.lit i),continuous_subtype_val.measurable.comp p.keeps,fun i g=>congrArg Subtype.val (p.gaugeX i g)⟩
def Bop (F G: Orbit n→ FC (Dwell n)):=F*G +(-1:ℂ) • (G*F)
lemma β_bop (i): Bop F G i=bump (F i) (G i):=by rw [Bop,neg_smul,one_smul]; rfl -- sub_eq_add_neg
local notation "P0"=> Portμ (citrus H S D) 0
lemma bopV(t:OpTheme S F false)(v: OpTheme S G false): OpTheme S (Bop F G) false:= opThemePlus (opThemeTimes t v) (opThemeScale _ (opThemeTimes v t))
lemma bopP(t:Portμ (citrus H S D) 0 F h c H.order)(v:Portμ (citrus H S D) 0 G h b H.order)(hc:0≤ c)(hb:0≤ b): P0 (Bop F G) h (2*(c*b)) H.order:=by
 have hp: ‖(-1:ℂ)‖*(b*c)=c*b:=by simp [mul_comm]
 rw [two_mul]; exact (t.mult v hc).add (hp ▸ (v.mult t hb).sMul (-1)) -- explicit norm.N
end lint
-- repeated commutator. curriculum.
variable {n:Side}{α:Type} (f:Orbit n→ FC (Dwell n))(g:α → Copy n)(k:List α)(P:BudgetPoint)(c:α→ℝ)(S D:Support (More n))
def Coral : Orbit n→FC (Dwell n):=fun i=>scar (f i) (k.map fun j=>g j i)
lemma Coral0 (t:OpTheme S f false)(hv:∀ i∈k,ThemeR S (g i)): OpTheme S (Coral f g k) false:=by
 induction k with
 | nil=> exact t
 | cons i L ih=>
    let z:=Bop (Coral f g L) (fun x=> (g i x).val)
    have he:Coral f g (i::L)=z:=funext fun x=> (β_bop (F:=Coral f g L) (G:=fun x=> (g i x).val) x).symm
    rw[he]; exact bopV (ih fun j h=> hv j (List.mem_cons_of_mem _ h)) (opThemeHold _ (hv i List.mem_cons_self))
variable {a d h:ℝ}{K:Support (More n)}
-- list costs exact $2^
local notation "P0"=> Portμ (citrus P S D) 0
lemma Coralμ0 (u:Portμ (citrus P S D) 0 f h a P.order)(p:∀ i∈k,Portμ (citrus P S D) 0 (fun x=>(g i x).val) h (c i) P.order)(v:∀ i∈k,0≤c i)(t:0≤a): P0 (Coral f g k) h ((2:ℝ)^k.length * a * (k.map c).prod) P.order:=by
 induction k with
 | nil=> simp only[List.map_nil,List.prod_nil,List.length_nil,pow_zero,mul_one,one_mul]; exact u
 | cons i L ih=>
    let z:=Bop (Coral f g L) (fun x=> (g i x).val)
    have he:Coral f g (i::L)=z:=funext fun x=> (β_bop (F:=Coral f g L) (G:=fun x=> (g i x).val) x).symm
    have hp:=p i List.mem_cons_self; have hc:=v i List.mem_cons_self; let G:= (2:ℝ)^L.length * a * (L.map c).prod; have hG:0≤ G:=mul_nonneg (mul_nonneg (by positivity) t) (List.prod_nonneg (fun j h=>by obtain ⟨i,t,rfl⟩:=List.mem_map.mp h; exact v i (List.mem_cons_of_mem _ t)))
    rw [he, List.length_cons,List.map_cons,List.prod_cons, show (2:ℝ)^(L.length+1) * a * (c i*(L.map c).prod)=2*(G*c i) from (by unfold G; rw [pow_succ]; ring)]; exact bopP (ih (fun j u=>p j (List.mem_cons_of_mem _ u)) (fun j t=>v j (List.mem_cons_of_mem _ t))) hp hG hc
lemma scar_one (v:γ→Dough ι)(q:γ→ℂ)(F:FC ι)(S:List γ): scar F (S.map fun i=>q i • v i)=(S.map q).prod • scar F (S.map v):=by
 induction S with
 |nil=>simp
 |cons i S ih=> rw [List.map_cons,List.map_cons,List.map_cons,scar,scar,ih]; change bump ((S.map q).prod • scar F (S.map v)) ((q i) • (v i).val)= _; rw [τb,τq,smul_smul,List.prod_cons]
end Ladder3
end Ivey
end YM.CF.Scree.Ing
end
