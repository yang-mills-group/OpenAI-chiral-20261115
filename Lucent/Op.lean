import Lucent.Score
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

variable {I:Type}
def glint (x:Tint I→ℝ)(f:List (Tint I)):ℂ:= (f.map fun i=>(x i:ℂ)).prod
lemma glint_append (x:Tint I→ℝ)(a b:List (Tint I)):glint x (a++b)=glint x a*glint x b:=by unfold glint; rw [List.map_append,List.prod_append]
lemma glint_nil (x:Tint I→ℝ):glint x []=1:= rfl
lemma glint_cons (x:Tint I→ℝ)(i:Tint I)(a:List (Tint I)):glint x (i::a)=x i*glint x a:=by rw [glint,List.map_cons,List.prod_cons]; rfl

abbrev hues {I:Type}(C:I→SU.group.Color) (v: Tint I):ℝ:=C v.1 v.2

def cell (N:Side)(x:Cover)(b:Twah.DirSpin)(i j:SU.Slot):FC (Single N):= create (basisC N x (upSpin b.1) i)*Fock.remove (basisC N x (dnSpin b.2) j)
def weave (N:Side)(x:I → Cover)(b:I→Twah.DirSpin)(f:List (Loop I)): FC (Single N):=(f.map fun i=>cell N (x i.1) (b i.1) i.2.1 i.2.2).prod

variable (N:Side) (W:I→ Staff) (S T :Stencil I)
-- placements
abbrev seat (W:I→ Staff)(i:I): Cover:= (W i).u
abbrev body (W:I→ Staff)(i:I): Twah.DirSpin:= (W i).spin
abbrev spind (N:Side)(W:I→ Staff) := weave N (seat W) (body W)

variable (G:I→SU.group.Color)
def knit (b: Join I): FC (Single N) := glint (hues G) b.flash • spind N W b.loom
def dream (N:Side)(W:I→Staff)(S:Stencil I)(G:I→SU.group.Color):FC (Single N):=S.quote (knit N W G)
lemma knit_glue (a b:Join I) : knit N W G (a.glue b)=knit N W G a*knit N W G b:=by
 unfold knit; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; simp only [spind,weave,List.map_append,List.prod_append, glint_append]
lemma dream_mul : dream N W (S*T) G = dream N W S G * dream N W T G := Stencil.quote_mulR S T _ (knit_glue N W G)
lemma mug_eq (a:SU.group.Color)(i:Pig): Hiro.mug.coord i a = a i:=by simp [Hiro.mug,Module.Basis.coord] -- check

open Buffered.Afterglow.Tower
-- colors and poses map. 
def crown (g:Seat N→SU.E) (G:I→SU.group.Color): I→SU.group.Color:=fun i=>SU.group.adjoint (g ((W i).scope N)) (G i)
def Singing (W:I→Staff)(S:Stencil I) : Prop:=∀ (N:Side) (G:I→SU.group.Color) (g:Seat N→SU.E), dream N W S (crown N W g G)= twist (quantU (tradew N g)) (dream N W S G)
-- activate as one supported weave
open Papal
def volley (r:ℕ)(ρ t:ℝ) (x:Pane N): I→SU.group.Color:= fun i=>(W i).pearl ρ N r t x

abbrev kite (r:ℕ)(ρ t:ℝ) (W:I→Staff)(S:Stencil I) : Papal.Weaver:= fun n x=>dream n W S (volley n W r ρ t x.1)
lemma volley_cov (c: Singing W S)(r:ℕ)(ρ t:ℝ)(n:Side): covariant (kite r ρ t W S n):=by
 intro g x; have h:volley n W r ρ t (simultaneous g x).1=crown n W g (volley n W r ρ t x.1):= funext fun i=>(W i).dockGauge ρ n r t x.1 g; unfold kite; rw [h,c n] -- ▸ 방향 
lemma kite_mul (r:ℕ)(ρ t:ℝ) : kite r ρ t W (S*T)=kite r ρ t W S*kite r ρ t W T:=funext fun _=>funext fun _=>dream_mul ..

variable (K:Calibration){A:Finset Cover}{r w:ℕ}(ρ t:ℝ)
def Charter (W:I→Staff)(A:Finset Cover)(r w:ℕ):Prop:=∀ i, (W i).Pays r w ∧ (W i).skyRent r⊆ A
lemma crew_budget (v: Charter W A r w)(L:List (Loop I)):InTest K true A false (fun m _=>spind (K.c m) W L):=by
 induction L with
 | nil=>exact .one
 | cons i L ih=>
   let D:=W i.1; let x:= D.u; let b:=D.spin; obtain ⟨t,g⟩:=v i.1
   have hv : nodeC x∈A:= g (pav_mono (show r ≤ r+8 by omega) (t.node D))
   let T : InTest K true A true (creation K x (upSpin b.1) i.2.1) := .creator _ (up_half _) hv
   let Q : InTest K true A true (removal K x (dnSpin b.2) i.2.2) := .remover _ (dn_half _) hv
   have h:(fun m (_:Fields (K.c m))=>spind (K.c m) W (i::L))=((creation K x (upSpin b.1) i.2.1)*(removal K x (dnSpin b.2) i.2.2))*fun m _=>spind (K.c m) W L:=by funext m y; unfold spind weave; rw [List.map_cons,List.prod_cons]; rfl
   rw [h]; exact (T.mul Q).mul ih

lemma sail_budget (v: Charter W A r w)(q: Join I) :InTest K true A false (fun m x=>knit (K.c m) W (volley (K.c m) W r ρ t x.1) q):=by
 obtain ⟨L,B⟩:=q; induction L with
 | nil=>
   have hp:(fun m (x:Fields (K.c m))=>knit _ W (volley _ W r ρ t x.1) ⟨[],B⟩)=(fun m _=>spind (K.c m) W B):=by funext m x; exact one_smul ℂ _
   rw [hp]; exact crew_budget W K v B
 | cons i L ih=>
   let J:=W i.1; let c:=J.docker ρ (v i.1).1 t i.2; let f:=((fun x:LinksC=>(Hiro.mug.coord i.2 (J.docked ρ r t x):ℂ)) ∘ (Prod.fst:PairsC→ LinksC))
   let V : Buffered.Family K:= fun m x=>knit (K.c m) W (volley (K.c m) W r ρ t x.1) ⟨i::L,B⟩
   let Z : Buffered.Family K:= fun m x=>knit (K.c m) W (volley (K.c m) W r ρ t x.1) ⟨L,B⟩
   have hp:V=scalar K f * Z:= by
      funext m x; unfold V Z scalar knit f; rw [show (⟨i::L,B⟩:Join I).flash=i::L from rfl,glint_cons,mul_smul,Pi.mul_apply,Pi.mul_apply,Algebra.smul_mul_assoc,one_mul]; dsimp only [Function.comp_apply]; rw [mug_eq,J.antenna]; rfl
   change InTest _ _ _ _ V; rw [hp]; exact (InTest.seed (c.mono (v _).2)).mul ih

lemma charter_price (v: Charter W A r w) :
    InTest K true A false (Papal.household K (kite r ρ t W S)):= by
 cases S with
 | mk L=> induction L with
   | nil=> exact .zero
   | cons q L ih=> exact ( (InTest.smul q.k (sail_budget W K ρ t v q.toJoin)).add ih) -- list sum defeq?
lemma singing_test (p:Singing W S)(v: Charter W A r w) : TestFamily K true (Papal.household K (kite r ρ t W S)) ∧ CovCover K (Papal.household K (kite r ρ t W S)):=by
 refine ⟨?_,fun m=>volley_cov W S p r ρ t _⟩
 exact aux_test (charter_price W S K ρ t v)
