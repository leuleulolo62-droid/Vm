-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'eDqol1AdA68I51Mb76eEiy0m'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-6ZvnHfultSoI
return Vm.run(__src, { name = 'RIVALS/Rivals', checksum = 2720453310, interval = 2, watermark = 'Y2k-6ZvnHfultSoI', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
