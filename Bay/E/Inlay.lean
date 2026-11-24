import Bay.E.Parlor

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family


/-- Assembly #Silk. first Pane inputs, charge on the actual letters;
    wind/collar an exact re-expression even on small panels meeting AtEase. -/
abbrev SiloIdx (α:Type)(o:Cover)(b:ℕ):= Option (α × Option (Beam (Band o b)×Beam (Band o b)))
abbrev Silo (α:Type)(o:Cover)(b:ℕ):= SiloIdx α o b → LinksC → ℂ
structure Foal (α:Type)(N:Side) where
 stem: α→Pane N→Op (Single N)
 spot: Pane N→Op (Single N)
variable {α:Type}{o:Cover}{b:ℕ}{N:Side}
local notation "S₀"=>Band o b

def hymnT (p:BudgetPoint)(k:ℕ)(d L:ℝ)(o:Cover)(G:Foal α N):Prop:=
  (∀i,Awning (G.stem i) p (wrap _ o) k L d)∧Awning G.spot p (wrap _ o) k L d
def ingo(o b)(g:Foal α N):Silo α o b
 | none=> Matrix.trace ∘ g.spot ∘ craft (Band o b) N
 | some (a,none)=> diagonal N ∘ g.stem a ∘ craft (Band o b) N
 | some (a,some (i,j))=> (fun x=>tariff N x i j) ∘ g.stem a ∘ craft (Band o b) N

def nipsN{α:Type}{o b}(N:Side)(f:Silo α o b):Mark N :=
 fun v=>f none (onC _ v.1) • 1
def winN{α:Type}{o b}(N:Side)(f:Silo α o b)(a:α): Mark N :=fun v=>
 f (some (a,none)) (onC _ v.1) • 1 +
  ∑ i,∑ j, f (some (a,some (i,j))) (onC _ v.1) • unitBlade _ i j
abbrev nips (K:Calibration)(f:Silo α o b):Ways K :=fun _=>nipsN _ f
abbrev wing (K:Calibration)(f:Silo α o b)(a:α):Ways K:=fun _=>winN _ f a

lemma flight (K:Calibration)(f:Silo α o b)(a:α) :
 wing K f a =
  weave K (f (some (a,none)))+∑ i:Beam S₀,∑ j:Beam S₀, weave K (f (some (a,some (i,j)))) * sword K i j :=by
 funext n v
 simp only[wing,winN,Pi.add_apply,Finset.sum_apply,Pi.mul_apply,weave,scalar,sword,
    comp_apply, Matrix.smul_mul, one_mul]
variable {p:BudgetPoint}{k:ℕ}{d L t:ℝ}
lemma inPay(hb:p.B=b)(ht:p.threshold=t)(k0:k≤b)(e:AtEase S₀ N)
 {g:Foal α N}(h:hymnT p k d L o g):
 ∀i,SilkPay o b t d L (ingo o b g i):=by

 rintro (_|⟨a,_|⟨i,j⟩⟩)
 · exact spool spoolZ h.2 hb ht k0 e
 · exact spool spoolDiag (h.1 _) hb ht k0 e
 exact spool (spoolTax ..) (h.1 a) hb ht k0 e

lemma inExact(hb:p.B=b)(k0:k≤b)(e:AtEase S₀ N)
 {g:Foal α N}(h:hymnT p k d L o g):
   nipsN _ (ingo o b g)=(fun v=>Matrix.trace (g.spot v.1) • 1) ∧
   ∀a,winN _ (ingo o b g) a=fun v=>preJ (tickA _) (g.stem a v.1):=by
 subst b
 refine ⟨funext fun v=>?_ ,fun a=>funext fun v=>?_⟩
 · simp only[nipsN,ingo,comp_apply]; rw [h.2.dep _ _ (craft_back e v.1)]
 dsimp only [winN,ingo,comp_apply]
 rw [(h.1 a).dep _ _ (craft_back e v.1)]
 apply preBlade (o:=o) (b:=p.B) e
 intro i j w
 obtain ⟨x,y⟩:=(h.1 a).light _ i j w
 exact ⟨modes_ch.mpr (roost_expand k0 (modes_ch.mp x)), modes_ch.mpr (roost_expand k0 (modes_ch.mp y))⟩ 

structure Hangs (t d L:ℝ)(r:ℕ→Silo α o b)(f:Silo α o b):Prop where
 owns:∀i n,SilkPay o b t d L (r n i)
 lands:∀i,SilkPay o b t d L (f i)
 earns:∀i,TendstoUniformly (fun n=>r n i) (f i) atTop

lemma Hangs.bloom (K:Calibration){r:ℕ→Silo α o b}{f:Silo α o b}(h:Hangs t d L r f):
 BQueue S₀ (fun n=>nips K (r n)) (nips K f) ∧
 ∀a,BQueue S₀ (fun n=>wing K (r n) a) (wing K f a):=by
 let x:=fun i=> qbSpun K (h.owns i) (h.lands i) (h.earns i)
 refine ⟨x none,fun a=>?_⟩
 simp_rw [flight]
 apply qbPlus (x _)
 refine qbSum _ fun i _=>qbSum _ fun j _=> ?_
 have h := (x (some (a,some (i,j)))).multiply (queSword K i j)
 rw [union_self] at h
 exact h

-- all subseqs
lemma hangar [Fintype α]{r:ℕ→Silo α o b}(v:∀n i,SilkPay o b t d L (r n i)):
   ∃φ:ℕ→ℕ, StrictMono φ ∧ ∃f,Hangs t d L (r∘φ) f:=by
 obtain ⟨φ,w,f,q⟩:=launch v
 exact ⟨φ,w,f,fun i n=>v ..,fun i=>(q i).1,fun i=>(q i).2⟩
end YM.CF.Bay.Silk
