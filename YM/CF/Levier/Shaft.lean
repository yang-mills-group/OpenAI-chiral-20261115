import YM.CF.Levier.Hooks
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
abbrev ray(b:Bool)(a:Shape):Sweep N:=⟨a.s,wrap N a.t,b⟩
lemma ray_join(t:Bool)(c:Shape): ray (N:=N) b a * ray t c = ray (b.xor t) (joinX a c):=by
 change Sweep.mk _ _ _= Sweep.mk (a.s*c.s) _ _; rw [show (joinX a c).t=a.s.act c.t+a.t from rfl,map_add,wrap_signed,add_comm]
lemma ray_i: ray k.charge (castX k)=k:=by unfold ray castX; rw [wrap_lift]
lemma crest_e(t s:Cover)(x:Signed)(p:wrap N t=wrap N s): gateC (N:=N) b (Shape.mk x t)=gateC b (Shape.mk x s):=by
 funext y i q; unfold gateC elf; simp_rw [funext (fun i=> stir_wrap i x t s p)]
lemma dartS (S:Seal (Site (More P))): roarD P ((castX (ray (N:=N) b a)).broad G) S=roarD P (a.broad G) S:=by
 let V:=castX (ray (N:=N) b a); have he: wrap P ((V.broad G).t)= wrap P ((a.broad G).t):=by simp only [Shape.broad,V,castX,← G.embed_wrap,wrap_lift]
 unfold roarD; exact congr_arg (fun e:Site _ → Site _=> S.image e) (funext fun i=> stir_wrap i a.s _ _ he)
lemma dartT : wish b (castX (ray (N:=N) b a)) G e= wish b a G e:=by
 let V:=castX (ray (N:=N) b a); have he:wrap N V.t=wrap N a.t:=wrap_lift _
 have hx:wrap P ((V.broad G).t)=wrap P (a.broad G).t:=by simp only [Shape.broad,← G.embed_wrap,he]
 funext x; have hp:gateC (N:=N) b V=gateC b a:=crest_e b _ _ a.s he -- tune
 have hv:gateC (N:=P) b (V.broad G)=gateC b (a.broad G):=crest_e b _ _ a.s hx
 exact Subtype.ext (Prod.ext (Prod.ext (congr_fun hv _) (congr_fun hp _)) (congr_fun hv _))
include h
lemma cloud_x(W:Op (Iota G))(t y:Cover)(s:Signed)(U:UNI SpinIdx)(hp: wrap N t=wrap N y): sings b (pflux ⟨s,t⟩ G U (xtra b)) W=sings b (pflux ⟨s,y⟩ G U (xtra b)) W:=by
 let V:= Shape.mk s t; let X:= Shape.mk s y
 let H:=pflux V G U (xtra b); let F:= pflux X G U (xtra b)
 have he: wrap P (V.broad G).t=wrap P (X.broad G).t:=by unfold V X Shape.broad; rw [← G.embed_wrap, hp,←G.embed_wrap]
 let z:= Rush.fee (periods P (V.broad G).t-periods P (X.broad G).t); have hx:H.val=z • F.val:=by unfold H F; rw [puff G h,puff G h,show (prepU (V.broad G) U (xtra b) P).val = z • (prepU (X.broad G) U (xtra b) P).val from utu P b U s _ _ he]; rfl
 have hz:z*star z=1:= by unfold z; rw [fee_real, fee_one]; -- tune
 change sings b H W=sings b F W; rw [singT,singT,twist_formula,twist_formula,hx,star_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
include h
abbrev steer(b:Bool)(w:Shape): Op (Iota G) →Op (Iota G):=sings b (pflux w G (spinU b w.s) (xtra b))
lemma steer_a(t:Bool)(c:Shape)(X:Op (Iota G)): steer G t c (steer G b a X)=steer G (b.xor t) (joinX a c) X:=by
 let U:=spinU b a.s; let V:=spinU t c.s; let W:=V*whiten t U; let F:=joinX a c; let S:=pflux F G (spinU (b.xor t) F.s) (xtra (b.xor t))
 let T:=pflux F G W (xtra (b.xor t)); have he:pflux c G V (xtra t) * whiten t (pflux a G U (xtra b))=T:=by
   apply Subtype.ext; rw [Submonoid.coe_mul,glint,puff G h,puff G h]; have ht (A:Op (Single P)):windX t (foot G A)=foot G (windX t A):=by cases t<;>rfl
   rw [ht,←glint,←foot_mul]; rw [show ((prepU _ V _ P).val)*(whiten t _).val= (siteU (joinX (Shape.broad G a) (Shape.broad G c)) (b.xor t) W P).val from congr_arg Subtype.val (turns P b (Shape.broad G a) U V _ t)]; unfold T F; rw [puff G h,←clan_b] -- tune args
 obtain ⟨z,hp,hz⟩:=kitsX (b.xor t) F.s W _ (shineU b a t U V c.s (spinZ ..) (spinZ ..)) (spinZ (b.xor t) F.s) -- tune shine order
 have hj:T.val = z • S.val:=by unfold T S; rw [puff G h,puff G h]; have hp:(prepU (F.broad G) W (xtra (b.xor t)) P).val=z • (prepU (F.broad G) (spinU (b.xor t) F.s) (xtra (b.xor t)) P).val:= Ygs _ _ _ hp; rw [hp]; rfl
 change sings t _ (sings b _ X)=sings _ _ _; rw [wake_r, show pflux _ _ _ _ * whiten _ _= T from he, singT,twist_formula]; change T.val*_*_= sings (b.xor t) S X; rw [hj,singT, twist_formula,star_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
end YM.CF.Levier
