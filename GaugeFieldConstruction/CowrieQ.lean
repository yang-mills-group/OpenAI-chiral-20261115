import GaugeFieldConstruction.TasmanQ
import GaugeFieldConstruction.SocorroQ
import GaugeFieldConstruction.WhelmQ
import GaugeFieldConstruction.WallabyQ
import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.BootHearthJ
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4200
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace WallsQ
variable {w:ℕ}{K:Calibration}{o:Cover}{m d:Side}
-- maximum over ANY value satisfying scored definition (not requiring color constants initial locations), empty profit 0. List enumeration.X
local instance (d:Side):NeZero (2*d.val):= ⟨(mul_pos (by decide) d.property).ne'⟩
local notation "DK"=> dialQ d
variable {C:Type} [Fintype C]{L:Loom (K.c m)}{E:Mark (K.c m)→ℂ}{Price:ℝ}
variable (D:Metered K m L E Price)
variable {col:C → Cover}{mtr:C→Family K}{S:C→Finset Cover}{A:C→ℝ}{u:C→ℝ}
variable (p₀: ∀ i,0 ≤ A i) (hu:∀ i, 0 < u i)
variable (e:∀ i:C, InTest K true (S i) false (mtr i)) (c:∀ i:C, pay (mtr i) (A i)) (h:∀ i,PipeQ K w o (col i) (S i))
variable {x:dialQ d→C}{M:dialQ d→Family K}
variable {Ω:List (dialQ d)}(l:useinQ Ω)
private lemma StakeOneQ {a b:Cover}{F:Family K}(t:StakeQ K w o a 1 b F):F=1:=by generalize he: (1:Family K)=X at t; induction t with|start=>rfl|bends i v p ih=>rw [ih,←he,mirror_unit]
lemma whyΨQ (d:Side)(v:List (dialQ d))(h:useinQ v):v.length=(2*d.val)^4:=by
 have e:v.toFinset=univ:=Finset.ext (fun i=>by simp [h.1 i]); have hp:=List.toFinset_card_of_nodup h.2 -- signatures
 rw [←hp,e,Finset.card_univ]; simp [dialQ,Fintype.card_congr,ZMod.card] -- tune
variable (z:CatellaQ K w o d (K.c m))
variable {Lx:List C}(hv: useinQ Lx)(p':Injective (buttonQ d∘col))
include D e c h z hv p' hu
lemma SteamQ (H':∀ i:C,∀ (Ω:List (dialQ d))(z:useinQ Ω)(V:dialQ d→Family K),(∀ t,TwigQ K w o (col i) (mtr i) d t (V t)) → ‖E ((Ω.map V).prod m)‖ ≤ (u i)^Ω.length):
 ‖E ((Lx.map mtr).prod m)‖≤ (Lx.map u).prod:=by
 let zA:=C ⊕ dialQ d
 let k(z:dialQ d):Cover:=fun i=> (z i).val; let V:=buttonQ d; have hk:(buttonQ d)∘k=id:= funext fun i=>by funext j; unfold buttonQ k Function.comp id; push_cast; simp
 let col':=Sum.elim col k; let f: zA→Family K:=Sum.elim mtr (fun _=>1); let u':zA→ℝ:=Sum.elim u (fun _=>1); let a:zA→ℝ:=Sum.elim A (fun _=>1); let g:zA→Finset Cover:=Sum.elim S (fun _=>∅)
 have q(i:zA):InTest K true (g i) false (f i)∧ PipeQ K w o (col' i) (g i) ∧ 0<u' i∧ pay (f i) (a i):=by
    cases i
    · exact ⟨e _,h _,hu _,c _⟩
    refine ⟨InTest.one,fun _ z v=>?_,zero_lt_one,pay_unit⟩; simp [g] at v
 let M:=buttonQ d ∘ col
 let x(t:dialQ d):zA:= if p:t∈ Set.range M then Sum.inl (p.choose) else Sum.inr t
 have hx(i:C):x (M i)=Sum.inl i:=by unfold x; rw[dif_pos (Set.mem_range_self _)]; congr; exact p' (Exists.choose_spec (Set.mem_range_self _))
 let J:= univ \ (univ.image M); let W:= J.toList; let Ω:=Lx.map M ++ W
 have hw:∀y:dialQ d,y∈W↔ y ∉ Set.range M:= by intro y; simp [W,J]
 have Ph(t)(j:t∈ W):x t=Sum.inr t:=by unfold x; rw[dif_neg ((hw _).1 j)]
 have hp:useinQ Ω:=by
    refine ⟨?_,List.nodup_append'.mpr ⟨hv.2.map p',Finset.nodup_toList _,fun i t r=> (hw _).1 r ?_⟩⟩
    · intro y
      by_cases t:y ∈ Set.range M
      · obtain ⟨i,rfl⟩:= t; exact List.mem_append_left _ (List.mem_map_of_mem (hv.1 _)) -- tune
      exact List.mem_append_right _ ((hw _).2 t)
    obtain ⟨v,k,rfl⟩:=List.mem_map.mp t; exact ⟨_,rfl⟩
 have pV:tentPegQ w o K col' f d x (f∘x):=by
    intro y
    unfold Function.comp; by_cases w':y∈W
    · rw [Ph _ w']; exact ⟨k y,congrFun hk y,.start⟩
    rw [hw] at w'
    push_neg at w'; obtain ⟨i,rfl⟩:= w' -- push_neg may ∀
    rw [hx]; exact ⟨col i,rfl,.start⟩
 have hz: ∀ i:zA,∀ V:dialQ d→Family K,(∀ t,TwigQ K w o (col' i) (f i) d t (V t)) → ‖E ((Ω.map V).prod m)‖ ≤ (u' i)^Ω.length:=by
    intro i v t
    cases i with
    | inl i=>exact H' i Ω hp v t
    | inr i=>
       have h:v=fun _=>1:=funext fun y=>by obtain ⟨_,_,e⟩:=t y; exact StakeOneQ e
       rw[h,List.map_const',List.prod_replicate,one_pow]; change ‖E 1‖≤_; rw [D.unit]; simp [u'] -- D.unit tune
 have ht:= tasselQ D (fun i=>(q i).2.2.1) (fun i=>(q i).1) (fun i=>(q i).2.2.2) (fun i=>(q i).2.1) hp z hz pV
 have hF(i:C): f (x (M i))=mtr i:=by rw[hx]; rfl
 have ha(i:C): u' (x (M i))=u i:=by rw[hx]; rfl
 have hg:(Ω.map (f∘x)).prod=(Lx.map mtr).prod:=by
    unfold Ω; rw[List.map_append,List.prod_append,List.map_map,show (f∘x)∘M=mtr from funext hF,show W.map (f∘x)=W.map (fun _=> 1) from List.map_congr_left (fun i p=>by rw [Function.comp_apply,Ph _ p]; rfl),List.map_const',List.prod_replicate,one_pow,mul_one]
 have hj:(Ω.map (u'∘x)).prod=(Lx.map u).prod:=by unfold Ω; rw[List.map_append,List.prod_append,List.map_map,show (u'∘x)∘M=u from funext ha,show W.map (u'∘x)=W.map (fun _=> 1) from List.map_congr_left (fun i p=>by rw [Function.comp_apply,Ph _ p]; rfl),List.map_const',List.prod_replicate,one_pow,mul_one]
 rwa [hg,hj] at ht
#print axioms SteamQ
end WallsQ
end YM.CF.Buffered.Afterglow.Tower.SlabMark
end
