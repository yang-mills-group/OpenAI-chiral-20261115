import YM.CF.Tulip.Metro
/-! Sewing the flux & holomorphy ports. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
-- geometry Ratio here denotes arbitrary fermionic dilation
variable {N P:Side}(G:Ratio N P)
abbrev Guy := Edge (Site (More N))
abbrev pathL (G:Ratio N P)(i:Axis): Walk:= straight i (G.count.val:ℤ)
def scaleG (g:Site (More P)→E): Site (More N)→E:= g ∘ (ratio G).embed
lemma mapsG (x:Site (More N))(i:Axis): (ratio G).embed (x+step i)=(ratio G).embed x + (G.count.val • step i):=by
  rw [← Ratio.root_embed,map_add,Ratio.root_embed, Ratio.root_embed,←wrap_step (More N), Ratio.embed_wrap,map_nsmul,wrap_step]; rfl
lemma bites (o i): stop (o:Site (More P)) (pathL G i) =o+ G.count.val • step i := by nth_rw 1 [← wrap_lift o]; rw [← wrap_stop_cover, straight_stop,map_add,map_zsmul,wrap_lift,wrap_step]; simp
lemma stopG (x:Site (More N))(i:Axis): stop ((ratio G).embed x) (pathL G i)=(ratio G).embed (x+step i):=by rw [mapsG,bites]
lemma pathGL(i:Axis): (pathL G i).length=G.count.val:=by simp [pathL,straight]

abbrev Nom (N P:Side):= Bkg (More P) × Bkg (More N)
abbrev Coil(N P:Side):= Chin P × Chin N

def unionP (i:Nom N P):Coil N P:= (profile i.1,profile i.2)
structure JointB (U:Nom N P)(e:ℝ) : Prop where
  fg : Cube.Guard U.1 e
  cg : Cube.Guard U.2 e
  follow (x: Guy (N:=N)): ‖brand (U.2 x)-brand (travel U.1 ((ratio G).embed x.1) (pathL G x.2))‖≤ e

def legal (e:ℝ):Set (Coil N P):={x|∃ U:Nom N P, JointB G U e∧ ‖x-unionP U‖< e}
lemma cabin (e:ℝ): IsOpen (legal G e) :=by rw [show legal G e= ⋃ U:{U: Nom N P//JointB G U e}, Metric.ball (unionP U.val) e by ext x; simp [legal,Metric.mem_ball,dist_eq_norm]]; exact isOpen_iUnion fun _=>isOpen_ball
lemma crests (e:ℝ)(h:0<e): 1∈legal G e:=by
  let U:Nom N P:=1; have hx (w:Walk)(x:Site (More P)): travel U.1 x w=1:= by
    induction w generalizing x with
    | nil=>rfl
    | cons a w ih=> rw [travel, ih]; rcases a with ⟨a,h|h⟩ <;> simp [U,Step.read]
  have he : JointB G U e:=by refine ⟨guard0 h.le,guard0 h.le,?_⟩; rintro ⟨x,i⟩; rw [hx]; change ‖brand 1-brand 1‖≤_; simp [h.le]
  exact ⟨U,he,by simp [unionP,U,profile_trivial,Prod.norm_def,h]⟩ -- tune
lemma leftL {x:Coil N P}{e}(h:x∈legal G e) : x.1∈ Openc _ e:=by obtain ⟨U,h,f⟩:= h; exact ⟨U.1,h.fg,(norm_fst_le (x-unionP U)).trans_lt f⟩
lemma rightL {x:Coil N P}{e}(h:x∈legal G e) : x.2∈Openc _ e:=by obtain ⟨U,h,f⟩:=h; exact ⟨U.2,h.cg,(norm_snd_le (x-unionP U)).trans_lt f⟩
lemma insideP {x:Coil N P}{a e}(h:x∈legal G a)(hp:a≤e): x∈ legal G e:=by obtain ⟨U,h,k⟩:=h; exact ⟨U,⟨h.fg.shrink hp,h.cg.shrink hp,fun x=>(h.follow x).trans hp⟩,k.trans_le hp⟩

def jazz (g:Site (More P)→ E)(x:Coil N P):Coil N P:=(relayg g x.1,relayg (scaleG G g) x.2)
def july (g:Site (More P)→ E)(U:Nom N P):Nom N P:=(gauge g U.1,gauge (scaleG G g) U.2)
lemma jig (g:Site (More P)→E)(U:Nom N P): unionP (july G g U)=jazz G g (unionP U):=by simp [jazz,july,unionP,profile_g]
lemma joint_g {e:ℝ}(U:Nom N P)(h:JointB G U e)(g:Site (More P)→E): JointB G (july G g U) e:=by
  refine ⟨h.fg.cov _,h.cg.cov _,?_⟩; rintro ⟨x,i⟩
  change ‖brand (scaleG G g x*_*(scaleG G g (x+step i))⁻¹)-brand (travel (gauge g _) _ _)‖≤_
  rw [travel_gauge,stopG]; simp only [scaleG,comp_apply,brand_mul,brand_inv,←sub_mul,←mul_sub,brand_rig,brand_lef]; exact h.follow (x,i)
lemma surface (g:Site (More P)→E)(e:ℝ){x:Coil N P}(h:x∈ legal G e): jazz G g x∈legal G e:=by
  obtain ⟨U,p,h⟩:=h; refine ⟨_,joint_g G _ p g,?_⟩; rw [jig,Prod.norm_def]; dsimp only [jazz,Prod.fst_sub,Prod.snd_sub]; rw [relayg_eq,relayg_eq]; exact h

def cloudG(S:Seal (Site (More P))): Seal (Site (More N)):=univ.filter fun i=>(ratio G).embed i∈S

def deal (S:Seal (Site (More P)))(x y:Coil N P):= fare S x.1 y.1+fare (cloudG G S) x.2 y.2
lemma deal_pos(S:Seal (Site (More P)))(x y:Coil N P):0≤deal G S x y:=add_nonneg (fare_t ..) (fare_t ..)
lemma deal_le {S T}(h:S⊆T)(x y):deal G S x y≤deal G T x y:=add_le_add (fare_inc h ..) (fare_inc (by unfold cloudG; intro i p; exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp p).2⟩) ..)
abbrev Iota := (Site N× St G.count)×Slot
def switchG : Iota G ≃ Single P:= (blast G).prodCongr (Equiv.refl _)
def tempo (e:ℝ):Stage (Site (More P)) (Iota G) ↥(legal G e) (Site (More P)→E) :=
  ⟨terr (More P),fun i=> node ((switchG G i).1.1),fun g x=>⟨_,surface G g _ x.property⟩,fun S x y=> deal G S x y / |e|,fun S x y=> div_nonneg (deal_pos ..) (abs_nonneg _),fun h x y=>div_le_div_of_nonneg_right (deal_le G h ..) (abs_nonneg _)⟩
def temper (e:ℝ) : Branch.Tag (tempo G e) where
  run t:= ⟨(tradew P t).val.submatrix (switchG G) (switchG G), Matrix.mem_unitaryGroup_iff'.mpr (by change (star (tradew P t).val).submatrix _ _ * _=1; rw [Matrix.submatrix_mul_equiv,show star (tradew P t).val*_ =1 from (tradew P t).property.1]; ext; simp [Matrix.one_apply])⟩
  keeps := fun g i j h=> (bail P e).keeps g _ _ h

def spur (g:Site (More P)→ E)(i:Site N×St G.count): UNI Slot := matter (g ((ratio G).embed (node i.1)))

def torch(e:ℝ): Branch.Tag (tempo G e) :=⟨fun t=> ⟨jump (Equiv.refl _) (fun i=> (spur G t i).val),jump_unitary _ _ (fun i=>(spur G t i).property)⟩,fun g ⟨i,a⟩ ⟨j,b⟩ h=> by
  have hh:i≠j:=by rintro rfl; exact h rfl
  simp [jump_apply,hh]⟩
lemma temper_form (t e): ((temper G e).run t).val= jump (Equiv.refl _) (fun (i:Site N×St G.count)=> (matter (t (node (((blast G) i).1)))).val):=by
  ext ⟨x,b⟩ ⟨y,c⟩; change (tradew P t).val _ _= _; simp [tradew, switchG, jump_apply]
lemma temper_cap (e):Capacity (tempo G e) quota :=by
  refine ⟨glen,fun i j=>(meterQ P e).ball i j,fun i j=>?_⟩
  let T:=board (tempo G e) (bay (terr _) i j); let W:= board (forum P e) (bay (terr _) i j)
  have he:T.image (switchG G)=W:=by
    ext k; obtain ⟨z,rfl⟩:= (switchG G).surjective k; simp only [mem_image, Equiv.apply_eq_iff_eq, exists_eq_right]; simp only [T,W,board, Finset.mem_filter,Finset.mem_univ,true_and]; exact Iff.rfl -- def tune
  change (T.card:ℝ)≤ _; rw [← card_image_of_injective T (Equiv.injective (switchG G)),he]; exact (meterQ P e).place ..
end YM.CF.Peaks
