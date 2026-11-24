import Zephyr.Chern.Bends
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Rush YM.Laurent


abbrev IS := SpinIdx × SU.Slot

def flag (N:Side)(x:Cover):ℂ:=fee (periods N x)

lemma flag_sq (N:Side)(x:Cover) : flag N x*flag N x=1:=fee_one _
lemma flag_norm (N:Side)(x:Cover) : ‖flag N x‖=1:=fee_norm _

def tag (N:Side)(x:Cover)(i:IS):Single N:=((wrap N x,i.1),i.2)

variable {N:Side}
/-- AP-lifted scalar entries. -/
def lint (P:Op (Single N))(x y:Cover)(i j:IS):ℂ :=
   flag N x*flag N y*P (tag N x i) (tag N y j)

def tap (F:Oil N)(A:StemA N)(x y:Cover)(i j:IS) (u:ℝ):=
  lint (F (profile (petals A u))) x y i j

def tuft (F:Oil N)(A:StemA N)(x y:Cover)(i j:IS):=
   bud (tap F A x y i j)

variable {a e r B W:ℝ}{F:Oil N}

lemma tap_wad (p:Solo a r F e)(he:0<e)
    (A:StemA N)(x y:Cover)(i j:IS):
    Bloom (tap F A x y i j) ((flag N x*flag N y) • wad F A (tag N x i) (tag N y j)) :=
  (solo_bud p he).bloom.scale _

lemma tuft_bloom (p:Solo a r F e)(he:0<e)
    (A:StemA N)(x y:Cover)(i j:IS) :
    Bloom (tap F A x y i j) (tuft F A x y i j):=
  (tap_wad p he ..).1.bloom

lemma pwin (N:Side)(j:IS) : book (tag N 0 j)=1:=by rw [book,tag,node_wrap];simp

lemma win_right (N:Side)(i:Single N)(j:IS) :
    Pillow 1 i (tag N 0 j) := Or.inr (pwin N _)

lemma tuft_norm (p:Solo a r F e)(he:0<e)(A:StemA N)(x y:Cover)(i j:IS)(k:Fin 3) :
    ‖tuft F A x y i j k‖= ‖wad F A (tag N x i) (tag N y j) k‖:=by
  rw [tuft,(tap_wad p he ..).bud_eq,Pi.smul_apply,norm_smul,norm_mul,flag_norm,flag_norm,
    one_mul,one_mul]

lemma tuft_fall (p:Solo a r F e)(w:Oily a e 16 W)
    (x:Cover)(v:lift (wrap N x)=x)(i j:IS)(k:Fin 3) :
    ‖tuft F (stream N) (-x) 0 i j k‖≤W*r * Real.exp (-(a/4) * size x) := by
  rw [tuft_norm p w.s.ready]
  have hr:0≤r := by obtain ⟨T⟩:=bough_exists p;exact T.led.posP
  let m:= separation (node (wrap N (-x))) 1
  refine (solo_fall p w (stream_mild N) (win_right _ _ _) m ?_ k).trans ?_
  · rw [pwin];exact le_rfl
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (mul_nonneg w.bound.le hr)
  linarith [mul_le_mul_of_nonneg_left (show (size x:ℝ)≤2*m from by exact_mod_cast under_node x v)
    w.hb.le]

lemma tuft_far_price (x:Cover)(ha:0<a)(he:0<e):
    ∃ Y:ℝ, 0<Y∧ ∀ (P:Side)(Q:Oil P), Solo a r Q e→∀ y i j k,
    ‖tuft Q (stream P) (-x) (-y) i j k‖ ≤ Y*r := by
  obtain ⟨Y,⟨u⟩⟩:= oily ha he ((16:ℝ)*(1+(↑(size ((2:ℕ) • -x)):ℝ)))
  refine ⟨Y,u.bound,?_⟩
  intro P Q p y i j k
  have h:separation (1:Site (More P)) (book (tag P (-x) i)) ≤ size ((2:ℕ) • -x):=by
    rw [separation_comm,book,tag,node_wrap,separation,add_sub_cancel_right]
    exact pdist_wrap ..
  rw [tuft_norm p he]
  exact solo_price p u ((stream_mild P).slide h) (Or.inl rfl) k

lemma tuft_fringe (p:Solo a r F e)
    (z x:Cover)(i j:IS)(k:Fin 3)(m:ℕ)(n:4*m+2*size z+1<N.val)
    (w:Oily a e (rim z) W):
    ‖tuft F (transA N z) (-x) 0 i j k - tuft F (glazed N z) (-x) 0 i j k‖ ≤
      2*(W*r*Real.exp (-(a/2)*m)) := by
  simp only [tuft,(tap_wad p w.s.ready ..).bud_eq, Pi.smul_apply,
    ←smul_sub,norm_smul,norm_mul,flag_norm,one_mul]
  exact solo_slit p w (trans_mild _ _) (glaze_mild _ _) (win_right _ _ _) m
    (glaze_trans z m n) k
