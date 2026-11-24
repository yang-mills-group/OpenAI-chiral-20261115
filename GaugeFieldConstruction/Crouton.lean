import GaugeFieldConstruction.CabalT
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux Zpress Hood
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
local instance VInst (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance VInstB (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
namespace ScopeU
variable {V P:Pane n→ FC (Single n)}{d l m v:ℕ}{A b c x e a f y:ℝ}{S' D: Support (More n)} {X R:Ropes n}
def chem (x y:Rope n):Rope n:=(ponder x.1 y.1,x.2++y.2)
def bounty(X R:Ropes n):Ropes n:= X.flatMap fun i=> R.map (chem i)
lemma Bar_D (X R:Ropes n)(F:Tick (More n) SU.group→ℝ): FrameP.dawn (bounty X R) F= FrameP.dawn X F * FrameP.dawn R F:=by
 have ht(x y:Rope n): FrameP.done (chem x y) F=FrameP.done x F* FrameP.done y F:=by
    have he: factorV ((chem x y).2) F = factorV x.2 F*factorV y.2 F:=by unfold chem factorV; simp
    unfold FrameP.done; rw [he,show motionF (chem x y).1= motionF x.1 *motionF y.1 from factor_p x.1 y.1, Complex.ofReal_mul,mul_smul,Algebra.smul_mul_assoc ((factorV x.2 F):ℂ), Algebra.mul_smul_comm ((factorV y.2 F):ℂ) (motionF x.1)]
 have hf (P Q: Ropes n):FrameP.dawn (P++Q) F=FrameP.dawn P F+FrameP.dawn Q F:=by unfold FrameP.dawn; simp
 have he(x:Rope n)(R:Ropes n): FrameP.dawn (R.map (chem x)) F=FrameP.done x F*FrameP.dawn R F:=by induction R with|nil=> simp [FrameP.dawn]|cons i R ih=> change FrameP.done _ F+FrameP.dawn (R.map _) F= _*(FrameP.done i F+_); rw [ht, mul_add,ih]; rfl
 induction X with|nil=> simp [FrameP.dawn,bounty]|cons i l ih=> change FrameP.dawn ((R.map (chem i))++bounty l R) F= (FrameP.done i F+FrameP.dawn l F)*_; rw [hf,he,ih,add_mul]
lemma relief_Q (X R:Ropes n): reliefR (bounty X R)= reliefR X*reliefR R:=by
 have he(i:Rope n)(R:Ropes n): reliefR (R.map (chem i))= ‖i.1.1‖*reliefR R:=by induction R with|nil=> simp [reliefR,meterK]|cons j R ih=> change ‖i.1.1*j.1.1‖+ reliefR (R.map (chem i))= _ * (‖j.1.1‖+ reliefR R); rw [norm_mul,ih,mul_add]
 have hp (x y:Ropes n): reliefR (x++y)= reliefR x+ reliefR y:=by unfold reliefR meterK; simp
 induction X with|nil=>simp [bounty,reliefR,meterK]|cons i K ih=> change reliefR (R.map (chem i)++bounty K R)= (‖i.1.1‖+ reliefR K)*_; rw [hp,he,ih,add_mul]
lemma relief_pos (X:Ropes n):0≤ reliefR X:=by induction X with|nil=> exact le_rfl|cons i X h=> exact add_nonneg (norm_nonneg i.1.1) h
lemma count_R{X1 Y1:Rope n}(p: Rubric S' m d X1)(q:Rubric S' m l Y1): Rubric S' m (d+l) (chem X1 Y1):=by
 refine ⟨?_,?_,fun i v=> List.mem_append.mp v|>.elim (p.2.2 i) (q.2.2 i)⟩
 · intro i h; subst_vars; rw [List.mem_singleton.mp h]; obtain ⟨h1,t,K⟩:= p.1 _ (List.mem_singleton_self _); obtain ⟨l,c,w⟩:=q.1 _ (List.mem_singleton_self _); change Even (X1.1.2++Y1.1.2).length∧(X1.1.2++Y1.1.2).length ≤ _∧_; rw [List.length_append]; exact ⟨h1.add l,add_le_add t c,fun j p=>List.mem_append.mp p|>.elim (K j) (w j)⟩
 rw [chem,List.length_append]; exact add_le_add p.2.1 q.2.1
lemma barouche {v₁:ℝ}(P: Reeds X m d S' x)(Q:Reeds R m l S' v₁): Reeds (bounty X R) m (d+l) S' (x*v₁):=by
 refine ⟨?_,?_⟩
 · intro i h; obtain ⟨j,p,v⟩:= List.mem_flatMap.mp h; obtain ⟨k,q,rfl⟩:=List.mem_map.mp v; exact count_R (P.1 j p) (Q.1 k q)
 change reliefR _ ≤_; rw [relief_Q]; exact mul_le_mul P.2 Q.2 (relief_pos _) ((relief_pos _).trans P.2) -- tune expects x≥0
lemma Conv_A {v' x':ℝ}(U:Telescope V S' x y m d A b c e X)(W:Telescope P S' x' v' m l A b c f R): Telescope (V*P) S' (x*x') (y*v') m (d+l) A b c (e*v'+(y+e)*f) (bounty X R):=by
 refine ⟨?_,barouche U.forecast W.forecast,fun i j t=>?_⟩
 · refine ⟨env_mult U.upright.face W.upright.face,fun x g=>by rw [Pi.mul_apply,Pi.mul_apply,U.upright.gauge,W.upright.gauge,map_mul],fun x=>mul_C (U.upright.holds x) (W.upright.holds x)⟩
 let T:=P i; let Y:=propSeed X A i; let H:=propSeed R A i; let W':=onPage n S'; have ht: pressedF W' d e (V i-Y):=U.grips i j t; have hx: pressedF W' d (y+e) Y:=by
    nth_rw 1 [show Y=V i+ - (V i-Y) from (by abel)] -- tune troublesome dependent.V
    apply add_C (U.upright.holds i); simpa using ScaleC ht (-1)
 rw [Pi.mul_apply, show propSeed (bounty _ _) _ _=Y * H from Bar_D .., show V i * P i -_= (V i-Y)*P i+Y*(P i-H) from (by noncomm_ring -- noncomm tune
                                                                                    )]; exact add_C (mul_C ht (W.upright.holds i)) (mul_C hx (W.grips i j t))
lemma enlarge_R(p: Reeds X m d S' x)(h:S' ⊆ D)(g:v≥d)(t:x≤a):Reeds X m v D a:=by
 refine ⟨fun i w=>?_,p.2.trans t⟩; obtain ⟨J,P,K⟩:=p.1 i w; refine ⟨fun i w=> ?_,P.trans g,fun i w=> ?_⟩
 · obtain ⟨k,f,b⟩:=J i w; exact ⟨k,f.trans g,fun j l=> Finset.mem_filter.mpr ⟨mem_univ _,h (Finset.mem_filter.mp (b j l)|>.2)⟩⟩
 have he:=K i w; exact ⟨h he.1,fun k=> ⟨(he.2 k).1,image_subset_image h (he.2 k).2⟩⟩
lemma inflate (U:Telescope V S' x y m d A b c e X)(t:S'⊆D)(g:v≥d)(l:x≤a)(p:y≤f)(r':ℝ)(w:e≤r'): Telescope V D a f m v A b c r' X:=by
 have ht:onPage n S'⊆onPage n D:=fun j w=> Finset.mem_filter.mpr ⟨mem_univ _,t (Finset.mem_filter.mp w|>.2)⟩; refine ⟨⟨U.upright.face,U.upright.gauge,fun i=> lift_C (U.upright.holds i) p g ht⟩,enlarge_R U.forecast t g l,?_⟩;
 intro z k h; apply lift_C _ w g ht; exact U.grips z (fun i u=> k i (fun l=>u (disjoint_of_subset_left t l))) (fun i x y=> h i (t x) (t y))
abbrev Unitrope (n:Side): Rope n:= ((1,[]),[])
abbrev waltz (n:Side):Ropes n:=[Unitrope n]
lemma compass_u :Telescope (1:Pane n→ Fock.FC (Single n)) S' 1 1 m d A b c 0 (waltz n):=by
 let G:=Unitrope n; let X:=G.1; let V:=1; refine ⟨?_,?_,?_⟩
 · refine ⟨⟨(show Measurable _ from (show Measurable (fun _:Pane n=> (1:FC (Single n))) from measurable_const)) ,1,fun i=>norm_one.le⟩,fun i p=>(map_one _).symm,fun i=>?_⟩; exact ⟨[X],fun j t=>by rw [List.mem_singleton.mp t]; exact ⟨⟨0,rfl⟩,Nat.zero_le _,nofun⟩,by simp [X,meterK,G,Unitrope],by simp [X,orchestrate,G,Unitrope,motionF,rollC]⟩
 · refine ⟨fun i v=> ?_,?_⟩; · rw [List.mem_singleton.mp v]; exact ⟨fun i v=>by rw [List.mem_singleton.mp v]; exact ⟨⟨0,rfl⟩,Nat.zero_le _,nofun⟩,Nat.zero_le _,nofun⟩
   simp [waltz,meterK,Unitrope]
 intro i k p; change pressedF _ _ _ (1-_); rw [show propSeed _ _ _=1 from ?_,sub_self]; exact Ø_C
 simp [propSeed, FrameP.dawn, FrameP.done,factorV, waltz, Unitrope,motionF,rollC] -- tune
-- products with specified parenthesization
abbrev Wash {I:Type*}(W:List I)(X:I→ Ropes n): Ropes n:=W.foldr (fun i l=> bounty (X i) l) (waltz n)
abbrev actWork {I:Type*}(W:List I)(F:I→ Pane n→FC (Single n)):= (W.map F).prod
-- inductive budgeting for m scaling all
variable {v' x':ℝ}
def leak (d: ℕ)(v w:ℝ): ℕ→ℝ
 | 0=>0
 | k+1=> w*v^d+(v+w)*leak d v w k
lemma many {I:Type*}(W:List I)(Toc:I→Pane n→FC (Single n))(R:I→Ropes n)(x:ℝ)(v e:ℝ)(L:∀ i∈ W,Telescope (Toc i) S' x v m l A b c e (R i))(vx:1≤x)(vt:1≤v)(he:0≤e)(hW:W.length ≤d): Telescope (actWork W Toc) S' (x^W.length) (v^W.length) m (l*W.length) A b c (leak d v e W.length) (Wash W R):=by
 induction W with
 | nil=>
    refine ?_; change Telescope 1 S' (x^0) (v^0) m (l*0) A b c 0 (waltz n); simp only [pow_zero,mul_zero]; exact compass_u -- has C parameter
 | cons i l' ih=>
    rw [List.length_cons,pow_succ',pow_succ',Nat.mul_succ,Nat.add_comm (l*l'.length)]; change Telescope (Toc i*actWork l' Toc) S' _ _ _ _ _ _ _ _ _; -- tune
    have h:l'.length≤d:=by simp only [List.length_cons] at hW; omega
    refine inflate (Conv_A (L i List.mem_cons_self) (ih (fun j v=> L j (List.mem_cons_of_mem _ v)) h)) (Subset.refl _) le_rfl le_rfl le_rfl _ (add_le_add_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ vt h) he) _)
end ScopeU
end ArtCart
end MastTin
end YM.CF.XGarden
end
