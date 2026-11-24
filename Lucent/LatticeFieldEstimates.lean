import Lucent.Mineral
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

open Regis.Head.Brecht Stencil

section
variable (g:Join I→ℂ)
variable {α β:Type*}[Fintype α][Fintype β]
private lemma distribute (H:α→Join I→ℂ)(T:Stencil I):
    T.quote (fun x=>∑ i,H i x)=∑ i, T.quote (H i):=by
 cases T with|mk L=>induction L with|nil=>simp [Stencil.quote]|cons x l ih=> rw [cons_q, ih]; simp_rw [cons_q]; rw [sum_add_distrib,smul_sum]

variable (A:α→Stencil I)(B:β→Stencil I)
private lemma packs: (pack univ A*pack univ B).quote g=∑ i,∑ j,(A i*B j).quote g:=by
 simp_rw [mul_q,pack_q]; refine sum_congr rfl fun i _=>distribute (fun j x=>(B j).quote (fun y=>g (x.glue y))) _
private lemma packs3 (T:Stencil I) : (pack univ A*pack univ B*T).quote g=∑ i,∑ j,(A i*B j*T).quote g:=by
 rw [mul_q,packs]; simp_rw [mul_q] -- tune
end
variable (i j k u v:I)
def V (i:I) :Stencil I:=pack univ fun p=>beaded [(i,p)] i (crest p)
def D (z:Window.Family)(k:I):Stencil I:= beaded [] k (metals z)
def G (u v:I):Stencil I:=pack univ (α:=Pig) fun p=> mono [(u,p),(v,p)] []

variable (d:FieldPlan I)(z:Window.Family)[Fintype I]
lemma prune (L:List (Tint I)):
 fdiv d L (V i * V j) =
     ∑ p:Pig,∑ q:Pig,
       Matrix.trace (crest p * crest q) *
       (twoc d i j * vell (fair d.hands) (L++[(i,p),(j,q)])):=by
 unfold fdiv V; rw [packs]
 exact sum_congr rfl fun p _=>sum_congr rfl fun q _=> duoc (crest p) (crest q) d [(i,p)] [(j,q)] L i j
def uFee (d:FieldPlan I)(i j:I):ℂ:= specter (d.hands i).shade (d.hands j).shade ((d.hands i).p - (d.hands j).p)
lemma vcut (L:Op Slot→Op Slot→ℂ)(a:ℂ)(c:ℂ)(h:∀ p:Pig,L (crest p) (crest p)=a):
 (∑ p:Pig,∑ q:Pig, L (crest p) (crest q) *
       (c * vell (fair d.hands) [(i,p),(j,q)]))= (Fintype.card Pig:ℂ) * a*c*uFee d i j:=by
 simp only [vell,List.length_cons,List.length_nil,fuel,nib,List.append_nil, fair,sch]
 simp only [apply_ite (fun x:ℝ=>(x:ℂ)),Complex.ofReal_one,Complex.ofReal_zero,ite_mul,mul_ite,mul_zero,zero_mul,mul_one,one_mul,add_zero,sum_ite_eq,mem_univ,ite_true,h,sum_const,nsmul_eq_mul,card_univ,uFee]
 ring
def wedge (d:FieldPlan I)(i j:I):ℂ:= (Fintype.card Pig:ℂ)*60*twoc d i j*uFee d i j
lemma price_V : faq d (V i*V j)=wedge d i j:= by rw [fdiv_nil,prune]; exact vcut i j d (fun X Y=>Matrix.trace (X*Y)) 60 (twoc d i j) crestTrace

lemma price_D : faq d (D z k)=0:= solo (metals z) d [] [] k
lemma price_allZ (h:moneyC d.roles i k=0):
 faq d (V i*V j*D z k)=(Fintype.card Pig:ℂ)* tally z*tria d i j k * uFee d i j:=by
 rw [← vcut i j d (fun X Y:Op Slot=>Matrix.trace (X*Y*metals z)) _ _ (iod z)]
 unfold V D faq; rw [packs3]
 exact sum_congr rfl fun p _=>sum_congr rfl fun q _=>viac (crest p) (crest q) (metals z) d [(i,p)] [(j,q)] [] [] i j k h
def sheer (d:FieldPlan I)(u v:I) :ℂ:=(Fintype.card Pig:ℂ)*uFee (I:=I) d u v
lemma price_G : faq d (G u v)=sheer d u v:=by
 rw [fdiv_nil]
 simp [G,fdiv,pack_q,mono_q,vell,fair,sch,fuel,nib,aria,germ,Emu.runes,claps,anatomize,spinC,offer,Fock.cval,sheer,uFee]

def hem (d:FieldPlan I)(u v i j:I):ℂ:= uFee d u i * uFee d v j + uFee d u j *uFee d v i
private lemma vross (p q n:Pig):
    vell (fair d.hands) [(u,n),(v,n),(i,p),(j,q)] =
      if p=q then uFee d u v*uFee d i j + if p=n then hem d u v i j else 0 else 0:=by
 simp only [vell,List.length_cons,List.length_nil,fuel,nib,List.append_nil,List.nil_append,List.cons_append,fair,sch,hem,uFee]
 split_ifs<;> first| (expose_names; subst_vars;contradiction)| (push_cast; ring)
theorem price_both :
 faq d (G u v * (V i*V j)) = sheer d u v*wedge d i j +
    (Fintype.card Pig:ℂ)*60*twoc d i j * hem d u v i j:=by
 have hv:faq d (G u v*(V i*V j))= ∑ n:Pig, fdiv d [(u,n),(v,n)] (V i*V j):=by 
    unfold faq G; rw [mul_q,pack_q]
    exact sum_congr rfl fun _ _=> (mono_q _ _ _)
 rw [hv]
 simp only [prune,List.singleton_append,List.cons_append,List.nil_append,vross,mul_ite,mul_zero,sum_ite_eq,mem_univ,ite_true,mul_add,sum_add_distrib, sum_ite_eq',sum_const,nsmul_eq_mul,card_univ,crestTrace,sheer,wedge]
 ring
#print axioms price_both
