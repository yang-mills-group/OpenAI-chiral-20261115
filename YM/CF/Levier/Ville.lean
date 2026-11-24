import YM.CF.Levier.Glance
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
open Proa Hake Pastry
abbrev Grave:Type:= Bool × Bool × Bool × Bool
abbrev carL(r:Grave):Bool:=r.2.2.1
abbrev beltG(r:Grave):Bool:=r.2.2.2
def giveX(i:Grave):Grave:=(i.2.1,i.1,beltG i,carL i)
def flingX(i:Grave)(b:Bool):Grave:=(i.1,i.2.1,(carL i).xor b,(beltG i).xor b)
lemma flee_p(i:Grave)(b c:Bool):flingX (flingX i b) c=flingX i (b.xor c):=by unfold flingX; simp [carL,beltG]
lemma flee_o(i:Grave):flingX i false=i:=by simp [flingX,carL,beltG]
def whorl(i:Grave)(S:Seal (Site (More P)))(x:cro G e):Op (Iota G):= if i.1 then 0 else halo G e S x
def veilT(W:Meter Grave G e):Meter Grave G e:=fun i S x=> if i.1=i.2.1 ∧ carL i≠beltG i then (2:ℂ)⁻¹ • (W i S x-star (W (giveX i) S (chillF G e x))+whorl G e i S x) else W i S x
abbrev oakN(G: Grave→Op κ): Oak κ:= fun b v t q=> G (b,v,t,q)
lemma tale (W: Grave→Op κ)(g:Bool)(t u:Bool)(p:t≠u)(h:KindX (soar (oakN G W))): W (g,g,t,u)+star (W (g,g,u,t))= (if g then 0 else 1) :=by
 ext i j; rw [Matrix.add_apply]; change _+star (W (g,g,u,t) j i)= _; cases g; swap
 · have hx:= h.1 (t,i) (u,j)
   change ((if t=u then 0 else cSignX t (W (true,true,t,u) i j))+(if u=t then 0 else cSignX u (W (true,true,u,t) j i)))=0 at hx; rw [if_neg p,if_neg (Ne.symm p)] at hx
   change _+star _=0; cases t<;>cases u; contradiction; exact hx; rw [←star_eq_zero]; rw [star_add,star_star]; exact hx; contradiction
 have hx:= h.2 (t,i) (u,j); change (if t=u then 0 else cSignX t (W (false,false,t,u) i j))+(if u=t then 0 else cSignX u (W (false,false,u,t) j i))= _ at hx; rw [if_neg p,if_neg (Ne.symm p)] at hx; by_cases v:i=j
 · subst j; cases t<;>cases u; contradiction; simpa [Matrix.one_apply,revertP,cSignX] using hx; -- inspect true
   have ht:=congrArg star hx; simpa [Matrix.one_apply,revertP,cSignX] using ht; contradiction
 cases t<;>cases u; contradiction; simpa [Matrix.one_apply,revertP,cSignX,v] using hx; have he:=congrArg star hx; simpa [Matrix.one_apply,revertP,cSignX,v] using he; contradiction
variable (W:Meter Grave G e)(x:cro G e)
lemma stern(he: chillF G e x=x)(Z: Grave→ Op κ)(c:KindX (soar (oakN G Z)))(p:∀ i,∑ S, W i S x= Z i)(i:Grave): ∑ S, veilT G e W i S x = Z i:=by
 rcases i with ⟨v,g,t,u⟩; unfold veilT; simp only [carL,beltG]; by_cases h:v=g∧t≠u; swap; · simp only [if_neg h]; rw [p]
 simp only [if_pos h,he]; obtain ⟨rfl,h⟩:=h; rw [←smul_sum, sum_add_distrib,sum_sub_distrib,←star_sum,p,p]; have ht:=tale G Z v t u h c
 let X:= if v then (0:Op κ) else 1; rw [show ∑ s,whorl G e (v,v,t,u) s x=X from ?_]
 · change _ • (Z (v,v,t,u)-star (Z (v,v,u,t))+X)= _; rw [←show Z _+star (Z _)=X from ht]; rw [show Z (v,v,t,u)-star _+(Z (v,v,t,u)+star (Z (v,v,u,t)))=(2:ℂ) • Z (v,v,t,u) by rw [two_smul]; abel]; rw [smul_smul]; norm_num
 cases v; exact halo_sum G e x; simp [whorl,X]
include h
lemma even_W(w:∀ i k S x,toSpin G k (W i S x)= W (flingX i (accent k)) (toRoar G k⁻¹ S) (toWish G e k x))(S:Seal (Site (More P)))(i:Grave): toSpin G k (veilT G e W i S x)= veilT G e W (flingX i (accent k)) (toRoar G k⁻¹ S) (toWish G e k x):=by
 let f:=toSpin G k; let T:=accent k; have hp : carL (flingX i T)=beltG (flingX i T) ↔ carL i=beltG i:=by unfold flingX carL beltG; simp only; simp -- tune
 unfold veilT; simp only [show flingX i (accent k)=flingX i T from rfl, ne_eq,hp,show (flingX i T).1=i.1 from rfl,show (flingX i T).2.1=i.2.1 from rfl]; split
 swap; exact w ..
 have he(A B C:Op κ): f ((2:ℂ)⁻¹ • (A-star B+C))=(2:ℂ)⁻¹ • (f A-star (f B)+f C):=by unfold f toSpin steer; simp only [singT,win_c,win_s,win_l,win_a,twist_scalar,map_add,map_sub,map_star]; congr 1; unfold cSignX; split; simp; rfl
 rw [show toSpin _ _ (_ • (_+_))=_ from he _ _ _, show giveX (flingX i T) = flingX (giveX i) T from rfl]; unfold f; simp_rw [w,wish_f]; congr 2; unfold whorl; simp only [show (flingX i T).1=i.1 from rfl]; split_ifs; unfold toSpin steer; rw [singT,win_z,map_zero]; exact halo_t G h e k _ _ _
end YM.CF.Levier
