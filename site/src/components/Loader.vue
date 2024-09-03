<template>
    <div class="loader-container">
        <div class="loader">&nbsp;</div>
    </div>
</template>


<script>
export default {
  name: "Loader",
};
</script>

<style scoped>


.loader-container {
  display: flex;
  justify-content: center;
  align-items: center;
  height: 100%;
  position: absolute;
  left: 0;
  right: 0;
  top: 0;
  bottom: 0;
  background: rgba(255 255 255 / 30%);
}

.loader {
  border: 8px solid #f3f3f3; /* Light grey */
  border-top: 8px solid #3498db; /* Blue */
  border-radius: 50%;
  width: 40px;
  height: 40px;
  animation: spin 1s linear infinite;
  margin: 2px 16px;
}

@keyframes spin {
  0% {
    transform: rotate(0deg);
  }
  100% {
    transform: rotate(360deg);
  }
}

</style>